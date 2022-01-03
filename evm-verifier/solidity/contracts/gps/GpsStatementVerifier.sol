// SPDX-License-Identifier: Apache-2.0.
pragma solidity ^0.6.11;

import "../cpu/CairoBootloaderProgram.sol";
import "../cpu/CairoVerifierContract.sol";
import "../cpu/MemoryPageFactRegistry.sol";
import "../interfaces/Identity.sol";
import "../PrimeFieldElement0.sol";
import "./GpsOutputParser.sol";

contract GpsStatementVerifier is
    GpsOutputParser,
    Identity,
    CairoBootloaderProgramSize,
    PrimeFieldElement0
{
    CairoBootloaderProgram bootloaderProgramContractAddress;
    MemoryPageFactRegistry memoryPageFactRegistry;
    CairoVerifierContract[] cairoVerifierContractAddresses;

    uint256 internal constant N_BUILTINS = 5;
    uint256 internal constant N_MAIN_ARGS = N_BUILTINS;
    uint256 internal constant N_MAIN_RETURN_VALUES = N_BUILTINS;

    /*
      Constructs an instance of GpsStatementVerifier.
      bootloaderProgramContract is the address of the bootloader program contract
      and cairoVerifierContracts is a list of cairoVerifiers indexed by their id.
    */
    constructor(
        address bootloaderProgramContract,
        address memoryPageFactRegistry_,
        address[] memory cairoVerifierContracts
    ) public {
        // 카이로 프로그램(uint256 배열)이 저장되어 있는 스마트 컨트랙트 
        bootloaderProgramContractAddress = CairoBootloaderProgram(bootloaderProgramContract);

        // 메모리 페이지 저장 컨트랙트??
        memoryPageFactRegistry = MemoryPageFactRegistry(memoryPageFactRegistry_);

        // 카이로 검증 컨트랙트 리스트 초기화
        cairoVerifierContractAddresses = new CairoVerifierContract[](cairoVerifierContracts.length);
        for (uint256 i = 0; i < cairoVerifierContracts.length; ++i) {
            cairoVerifierContractAddresses[i] = CairoVerifierContract(cairoVerifierContracts[i]);
        }
    }

    function identify() external pure override returns (string memory) {
        return "StarkWare_GpsStatementVerifier_2021_3";
    }

    /*
      Verifies a proof and registers the corresponding facts.
      cairoAuxInput구조는 cpu/CpuPublicInputOffsets.sol 코드 참고
      taskMetadata 구조:
        1. Task 수.
        2. 각 task 구조:
            1. Task output 크기 (프로그램 해시 및 크기 포함).
            2. 프로그램 해시.
    */

    // 데이터 저장 위치가 memory, storage, calldata가 존재함 
    // calldata는 memory와 거의 비슷하게 동작함
    function verifyProofAndRegister(uint256[] calldata proofParams, uint256[] calldata proof, uint256[] calldata taskMetadata, uint256[] calldata cairoAuxInput, uint256 cairoVerifierId) external {
      // 카이로 검증 컨트랙트가 존재하는지 확인 (해당하는 index인지 확인)
      require(cairoVerifierId < cairoVerifierContractAddresses.length, "cairoVerifierId is out of range.");

      // 카이로 검증자 선택
      CairoVerifierContract cairoVerifier = cairoVerifierContractAddresses[cairoVerifierId];

      // z와 alpha 값은 메인 페이지의 fact 등록에만 사용됨 (아마 마지막 2개 uint256 값)
      // CpuVerifier에서 계산됨으로 CpuVerifier의 cairoPublicInput에 포함하지 않음 
      // cairoAuxInput에서 관련된 slice를 가져옴
      uint256[] calldata cairoPublicInput = (cairoAuxInput[:cairoAuxInput.length - 2]);

      uint256[] memory publicMemoryPages;
      {
        // publicMemoryOffset: 20 (상수)
        // selectedBuiltins: 31 (상수)
        (uint256 publicMemoryOffset, uint256 selectedBuiltins) = cairoVerifier.getLayoutInfo();

        require(cairoAuxInput.length > publicMemoryOffset, "Invalid cairoAuxInput length.");

        publicMemoryPages = (uint256[])(cairoPublicInput[publicMemoryOffset:]);

        uint256 nPages = publicMemoryPages[0]; // 페이지 수를 나타냄?
        // publicMemoryPages[0]: 페이지 수
        // publicMemoryPages[1]: 메모리 길이
        // publicMemoryPages[2]: 메모리 해시
        // publicMemoryPages[nPages * 3]: 누적 제품? -  Cumulative 란 의미 자체가 "누적된" 의미이므로 여태까지 업데이트 해야 할 것을 모두 포함 시켜 놓았는 듯?

        // 각 페이지는 페이지 정보 및 해시를 가짐
        // PAGE_INFO_SIZE = 3
        require(publicMemoryPages.length == nPages * (PAGE_INFO_SIZE + 1), "Invalid publicMemoryPages length.");

        // public memory main page 등록.
        (uint256 publicMemoryLength, uint256 memoryHash, uint256 prod) = registerPublicMemoryMainPage(taskMetadata, cairoAuxInput, selectedBuiltins);

        // 검증
        // PAGE_INFO_SIZE_OFFSET = 1
        // PAGE_INFO_HASH_OFFSET = 2
        // PAGE_INFO_SIZE = 3
        require(publicMemoryPages[PAGE_INFO_SIZE_OFFSET] == publicMemoryLength, "Invalid size for memory page 0.");
        require(publicMemoryPages[PAGE_INFO_HASH_OFFSET] == memoryHash, "Invalid hash for memory page 0.");
        require(publicMemoryPages[nPages * PAGE_INFO_SIZE] == prod, "Invalid cumulative product for memory page 0.");
      }

      // NOLINTNEXTLINE: reentrancy-benign.
      cairoVerifier.verifyProofExternal(proofParams, proof, (uint256[])(cairoPublicInput));

      registerGpsFacts(taskMetadata, publicMemoryPages, cairoAuxInput[OFFSET_OUTPUT_BEGIN_ADDR]);
    }

    /*
      Registers the fact for memory page 0, which includes:
      1. The bootloader program,
      2. Arguments and return values of main()
      3. Some of the data required for computing the task facts. which is represented in taskMetadata.
      Returns information on the registered fact.

      Arguments:
        selectedBuiltins: A bit-map of builtins that are present in the layout. See CairoVerifierContract.sol for more information.
        taskMetadata: Per task metadata.
        cairoAuxInput: Auxiliary input for the cairo verifier.

      Assumptions: cairoAuxInput is connected to the public input, which is verified by cairoVerifierContractAddresses.
      Guarantees: taskMetadata is consistent with the public memory, with some sanity checks.
    */
    function registerPublicMemoryMainPage(uint256[] calldata taskMetadata, uint256[] calldata cairoAuxInput, uint256 selectedBuiltins) internal returns (uint256 publicMemoryLength, uint256 memoryHash, uint256 prod) {
      // taskMetadata[0]: task 수
      uint256 nTasks = taskMetadata[0];

      // task 수가 2^30 개보다 작아야함
      require(nTasks < 2**30, "Invalid number of tasks.");

      // 메모리 길이
      // PROGRAM_SIZE = 216
      // N_MAIN_ARGS = 5
      // N_MAIN_RETURN_VALUES = 5
      // N_WORDS_PER_PUBLIC_MEMORY_ENTRY = 2
      publicMemoryLength = (PROGRAM_SIZE + 2 + N_MAIN_ARGS + N_MAIN_RETURN_VALUES + 1 + 2 * nTasks);
      uint256[] memory publicMemory = new uint256[](N_WORDS_PER_PUBLIC_MEMORY_ENTRY * publicMemoryLength);

      uint256 offset = 0;

      // Write public memory, which is a list of pairs (address, value).
      // 메모리에 프로그램 실행 코드 적재 !?
      // INITIAL_PC = 1
      {
        // Program segment.
        uint256[PROGRAM_SIZE] memory bootloaderProgram = bootloaderProgramContractAddress.getCompiledProgram();

        for (uint256 i = 0; i < bootloaderProgram.length; i++) {
          publicMemory[offset] = i + INITIAL_PC;
          publicMemory[offset + 1] = bootloaderProgram[i];
          offset += 2;
        }
      }

      {
        // Execution segment - Make sure [initial_fp - 2] = initial_fp and .
        // This is required for the "safe call" feature (that is, all "call" instructions will return, even if the called function is malicious).
        // It guarantees that it's not possible to create a cycle in the call stack.

        // OFFSET_EXECUTION_BEGIN_ADDR = 6
        uint256 initialFp = cairoAuxInput[OFFSET_EXECUTION_BEGIN_ADDR];

        require(initialFp >= 2, "Invalid execution begin address.");
        publicMemory[offset + 0] = initialFp - 2;
        publicMemory[offset + 1] = initialFp;
        // Make sure [initial_fp - 1] = 0.
        publicMemory[offset + 2] = initialFp - 1;
        publicMemory[offset + 3] = 0;
        offset += 4;

        // Execution segment: Enforce main's arguments and return values.
        // Note that the page hash depends on the order of the (address, value) pair in the
        // publicMemory and consequently the arguments must be written before the return values.
        uint256 returnValuesAddress = cairoAuxInput[OFFSET_EXECUTION_STOP_PTR] - N_BUILTINS;
        uint256 builtinSegmentInfoOffset = OFFSET_OUTPUT_BEGIN_ADDR;

        for (uint256 i = 0; i < N_BUILTINS; i++) {
          // Write argument address.
          publicMemory[offset] = initialFp + i;
          uint256 returnValueOffset = offset + 2 * N_BUILTINS;

          // Write return value address.
          publicMemory[returnValueOffset] = returnValuesAddress + i;

          // Write values.
          if ((selectedBuiltins & 1) != 0) {
            // Set the argument to the builtin start pointer.
            publicMemory[offset + 1] = cairoAuxInput[builtinSegmentInfoOffset];
            // Set the return value to the builtin stop pointer.
            publicMemory[returnValueOffset + 1] = cairoAuxInput[builtinSegmentInfoOffset + 1];
            builtinSegmentInfoOffset += 2;
          } else {
            // Builtin is not present in layout, set the argument value and return value to 0.
            publicMemory[offset + 1] = 0;
            publicMemory[returnValueOffset + 1] = 0;
          }
          offset += 2;
          selectedBuiltins >>= 1;
        }
        require(selectedBuiltins == 0, "SELECTED_BUILTINS_VECTOR_IS_TOO_LONG");
        // Skip the return values which were already written.
        offset += 2 * N_BUILTINS;
      }

      // Program output.
      {
        // Check that there are enough range checks for the bootloader builtin validation.
        // Each builtin is validated for each task and each validation uses one range check.
        require(cairoAuxInput[OFFSET_RANGE_CHECK_STOP_PTR] >= cairoAuxInput[OFFSET_RANGE_CHECK_BEGIN_ADDR] + N_BUILTINS * nTasks, "Range-check stop pointer should be after all range checks used for validations.");

        {
          uint256 outputAddress = cairoAuxInput[OFFSET_OUTPUT_BEGIN_ADDR];
          // Force that memory[outputAddress] = nTasks.
          publicMemory[offset + 0] = outputAddress;
          publicMemory[offset + 1] = nTasks;
          offset += 2;
          outputAddress += 1;

          uint256[] calldata taskMetadataSlice = taskMetadata[METADATA_TASKS_OFFSET:];
          for (uint256 task = 0; task < nTasks; task++) {
            uint256 outputSize = taskMetadataSlice[METADATA_OFFSET_TASK_OUTPUT_SIZE];
            require(2 <= outputSize && outputSize < 2**30, "Invalid task output size.");
            uint256 programHash = taskMetadataSlice[METADATA_OFFSET_TASK_PROGRAM_HASH];
            uint256 nTreePairs = taskMetadataSlice[METADATA_OFFSET_TASK_N_TREE_PAIRS];
            require(1 <= nTreePairs && nTreePairs < 2**20, "Invalid number of pairs in the Merkle tree structure.");
            // Force that memory[outputAddress] = outputSize.
            publicMemory[offset + 0] = outputAddress;
            publicMemory[offset + 1] = outputSize;
            // Force that memory[outputAddress + 1] = programHash.
            publicMemory[offset + 2] = outputAddress + 1;
            publicMemory[offset + 3] = programHash;
            offset += 4;
            outputAddress += outputSize;
            taskMetadataSlice = taskMetadataSlice[METADATA_TASK_HEADER_SIZE + 2 * nTreePairs:];
          }
          require(taskMetadataSlice.length == 0, "Invalid length of taskMetadata.");
          require(cairoAuxInput[OFFSET_OUTPUT_STOP_PTR] == outputAddress, "Inconsistent program output length.");
        }
      }

    require(publicMemory.length == offset, "Not all Cairo public inputs were written.");

    uint256 z = cairoAuxInput[cairoAuxInput.length - 2];
    uint256 alpha = cairoAuxInput[cairoAuxInput.length - 1];
    bytes32 factHash;

    // K_MODULUS = 0x800000000000011000000000000000000000000000000000000000000000001
    (factHash, memoryHash, prod) = memoryPageFactRegistry.registerRegularMemoryPage(publicMemory, z, alpha, K_MODULUS);
  }
}
