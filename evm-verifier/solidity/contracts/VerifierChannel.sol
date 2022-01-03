// SPDX-License-Identifier: Apache-2.0.
pragma solidity ^0.6.11;

import "./Prng.sol";

contract VerifierChannel is Prng {
  /*
      We store the state of the channel in uint256[3] as follows:
      [0] proof pointer.
      [1] prng digest.
      [2] prng counter.
  */
  uint256 private constant CHANNEL_STATE_SIZE = 3;

  event LogValue(bytes32 val);
  event SendRandomnessEvent(uint256 val);
  event ReadFieldElementEvent(uint256 val);
  event ReadHashEvent(bytes32 val);

  function getPrngPtr(uint256 channelPtr) internal pure returns (uint256) {
    return channelPtr + 0x20;
  }

  function initChannel(uint256 channelPtr,uint256 proofPtr,bytes32 publicInputHash) internal pure {
    assembly {
      // Skip 0x20 bytes length at the beginning of the proof.
      mstore(channelPtr, add(proofPtr, 0x20))
    }

    initPrng(getPrngPtr(channelPtr), publicInputHash);
  }

  function sendFieldElements(uint256 channelPtr, uint256 nElements, uint256 targetPtr) internal pure {
    require(nElements < 0x1000000, "Overflow protection failed.");
    assembly {
      // 3618502788666131213697322783095070105623107215331596699973092056135872020481
      let PRIME := 0x800000000000011000000000000000000000000000000000000000000000001

      let PRIME_MON_R_INV := 0x40000000000001100000000000012100000000000000000000000000000000
      let PRIME_MASK := 0x0fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
      
      let digestPtr := add(channelPtr, 0x20)
      let counterPtr := add(channelPtr, 0x40)

      let endPtr := add(targetPtr, mul(nElements, 0x20))

      // 시작 포인터(주소)부터 종료 포인터(주소) 까지
      // 하나의 워드는 32바이트 이므로 / targetPtr := add(targetPtr, 0x20) / 한 워드 이동
      for {} lt(targetPtr, endPtr) {targetPtr := add(targetPtr, 0x20)} {
        let fieldElement := PRIME

        // iszero(x) => x가 0 이면 1 / 아니면 0
        // lt(x, y) => x가 y보다 작으면 1 / 아니면 0
        for {} iszero(lt(fieldElement, PRIME)) {} {
          // keccak256(p, n) => 메모리 p 주소부터 p + n 주소까지의 데이터를 keccak 해시함
          // and(x, y) =>	x와 y를 and 비트 연산함
          fieldElement := and(keccak256(digestPtr, 0x40), PRIME_MASK)

          // mload(p) => 메모리 p 주소부터 p + 32 주소까지의 데이터를 로드함 (한워드)
          // and(x, y) =>	x와 y를 and 비트 연산함
          mstore(counterPtr, add(mload(counterPtr), 1))
        }
        // mulmod(x, y, m) => (x * y) % m with arbitrary precision arithmetics
        mstore(targetPtr, mulmod(fieldElement, PRIME_MON_R_INV, PRIME))
      }
    }
  }

  /*
    Sends random queries and returns an array of queries sorted in ascending order.
    Generates count queries in the range [0, mask] and returns the number of unique queries.
    Note that mask is of the form 2^k-1 (for some k).

    Note that queriesOutPtr may be (and is) inteleaved with other arrays. The stride parameter is passed to indicate the distance between every two entries to the queries array, 
    i.e. stride = 0x20*(number of interleaved arrays).

    임의의 쿼리를 보내고 오름차순으로 정렬된 쿼리 배열을 반환합니다.
    [0, mask] 범위에서 카운트 쿼리를 생성하고 고유한 쿼리 수를 반환합니다.
    마스크는 2^k-1(일부 k의 경우) 형식입니다.

    queryOutPtr은 다른 배열과 함께 삽입될 수 있습니다. 
    stride 매개변수는 쿼리 배열에 대한 모든 두 항목 사이의 거리를 나타내기 위해 전달됩니다.
    즉, stride = 0x20*(인터리브된 배열의 수).
  */
  function sendRandomQueries(uint256 channelPtr, uint256 count, uint256 mask, uint256 queriesOutPtr, uint256 stride) internal pure returns (uint256) {
    uint256 val;
    uint256 shift = 0;
    uint256 endPtr = queriesOutPtr;
    for (uint256 i = 0; i < count; i++) {
      if (shift == 0) {
        val = uint256(getRandomBytes(getPrngPtr(channelPtr)));
        shift = 0x100;
      }
      shift -= 0x40;
      uint256 queryIdx = (val >> shift) & mask;
      uint256 ptr = endPtr;
      uint256 curr;
      // Insert new queryIdx in the correct place like insertion sort.

      while (ptr > queriesOutPtr) {
        assembly { curr := mload(sub(ptr, stride)) }

        if (queryIdx >= curr) { break; }

        assembly { mstore(ptr, curr) }
        ptr -= stride;
      }

      if (queryIdx != curr) {
        assembly { mstore(ptr, queryIdx) }
        endPtr += stride;
      } else {
        // Revert right shuffling.
        while (ptr < endPtr) {
          assembly {
            mstore(ptr, mload(add(ptr, stride)))
            ptr := add(ptr, stride)
          }
        }
      }
    }

    return (endPtr - queriesOutPtr) / stride;
  }

  function readBytes(uint256 channelPtr, bool mix) internal pure returns (bytes32) {
    uint256 proofPtr;
    bytes32 val;

    assembly {
      // mload(p): 메모리의 특정 위치(p)에 있는 32바이트(1 워드)를 읽음
      proofPtr := mload(channelPtr)
      val := mload(proofPtr)
      
      // mstore(p, v): 메모리의 특정 위치(p)에 v를 저장
      
      // 포인터 이동
      mstore(channelPtr, add(proofPtr, 0x20))
    }
    if (mix) {
      assembly {
        let digestPtr := add(channelPtr, 0x20)
        let counterPtr := add(digestPtr, 0x20)
        
        // 왜하지??
        mstore(counterPtr, val)
        mstore(digestPtr, keccak256(digestPtr, 0x40))
        mstore(counterPtr, 0)
      }
    }

    return val;
  }

  function readHash(uint256 channelPtr, bool mix) internal pure returns (bytes32) {
    bytes32 val = readBytes(channelPtr, mix);

    return val;
  }

  function readFieldElement(uint256 channelPtr, bool mix) internal pure returns (uint256) {
    uint256 val = fromMontgomery(uint256(readBytes(channelPtr, mix)));

    return val;
  }

  function verifyProofOfWork(uint256 channelPtr, uint256 proofOfWorkBits) internal pure {
    if (proofOfWorkBits == 0) {
      return;
    }

    uint256 proofOfWorkDigest;
    assembly {
      // [0:29] := 0123456789abcded || digest || workBits.
      mstore(0, 0x0123456789abcded000000000000000000000000000000000000000000000000)
      let digest := mload(add(channelPtr, 0x20))
      mstore(0x8, digest)
      mstore8(0x28, proofOfWorkBits)
      mstore(0, keccak256(0, 0x29))

      let proofPtr := mload(channelPtr)
      mstore(0x20, mload(proofPtr))
      // proofOfWorkDigest:= keccak256(keccak256(0123456789abcded || digest || workBits) || nonce).
      proofOfWorkDigest := keccak256(0, 0x28)

      mstore(0, digest)
      // prng.digest := keccak256(digest||nonce), nonce was written earlier.
      mstore(add(channelPtr, 0x20), keccak256(0, 0x28))
      // prng.counter := 0.
      mstore(add(channelPtr, 0x40), 0)

      mstore(channelPtr, add(proofPtr, 0x8))
    }

    uint256 proofOfWorkThreshold = uint256(1) << (256 - proofOfWorkBits);
    require(proofOfWorkDigest < proofOfWorkThreshold, "Proof of work check failed.");
  }
}
