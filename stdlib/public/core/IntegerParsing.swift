//===----------------------------------------------------------------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2017 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

extension FixedWidthInteger {
  /// Creates a new integer value from the given string and radix.
  ///
  /// The string passed as `text` may begin with a plus or minus sign character
  /// (`+` or `-`), followed by one or more numeric digits (`0-9`) or letters
  /// (`a-z` or `A-Z`). Parsing of the string is case insensitive.
  ///
  ///     let x = Int("123")
  ///     // x == 123
  ///
  ///     let y = Int("-123", radix: 8)
  ///     // y == -83
  ///     let y = Int("+123", radix: 8)
  ///     // y == +83
  ///
  ///     let z = Int("07b", radix: 16)
  ///     // z == 123
  ///
  /// If `text` is in an invalid format or contains characters that are out of
  /// bounds for the given `radix`, or if the value it denotes in the given
  /// `radix` is not representable, the result is `nil`. For example, the
  /// following conversions result in `nil`:
  ///
  ///     Int(" 100")                       // Includes whitespace
  ///     Int("21-50")                      // Invalid format
  ///     Int("ff6600")                     // Characters out of bounds
  ///     Int("zzzzzzzzzzzzz", radix: 36)   // Out of range
  ///
  /// - Parameters:
  ///   - text: The ASCII representation of a number in the radix passed as
  ///     `radix`.
  ///   - radix: The radix, or base, to use for converting `text` to an integer
  ///     value. `radix` must be in the range `2...36`. The default is 10.
  @inlinable @inline(__always)
  public init?<S : StringProtocol>(_ text: S, radix: Int = 10) {
    precondition(2...36 ~= radix)
    let result_: Self?
    if let text = text as? String, text._guts.isSmall {
      result_ = _parseSmall(text._guts.rawBits, radix: radix)
    } else {
      result_ = text.utf8.withContiguousStorageIfAvailable { utf8 -> Self? in
        var iter = utf8.makeIterator()
        return _parseFromUTF8Inlined(&iter, radix: radix)
      } ?? {
        var iter = text.utf8.makeIterator()
        return _parseFromUTF8(&iter, radix: radix)
      }()
    }
    guard _fastPath(result_ != nil), let result = result_ else { return nil }
    self = result
  }

  /// Creates a new integer value from the given string.
  ///
  /// The string passed as `description` may begin with a plus or minus sign
  /// character (`+` or `-`), followed by one or more numeric digits (`0-9`).
  ///
  ///     let x = Int("123")
  ///     // x == 123
  ///
  /// If `description` is in an invalid format, or if the value it denotes in
  /// base 10 is not representable, the result is `nil`. For example, the
  /// following conversions result in `nil`:
  ///
  ///     Int(" 100")                       // Includes whitespace
  ///     Int("21-50")                      // Invalid format
  ///     Int("ff6600")                     // Characters out of bounds
  ///     Int("10000000000000000000000000") // Out of range
  ///
  /// - Parameter description: The ASCII representation of a number.
  @inlinable
  public init?(_ description: String) {
    self.init(description, radix: 10)
  }
}

@inlinable @inline(__always)
internal func _parseSmall<Result : FixedWidthInteger>(
  _ rawGuts: _StringObject.RawBitPattern, radix: Int
) -> Result? {
  // We work with the bytes as they are arranged in the StringObject,
  // i.e. the leading characters are in the least-significant bits.
  // This is as opposed to SmallString order, which swaps them on big-endian
  // platforms to maintain the same in-memory order.
  var word1 = rawGuts.0
  let word2 = rawGuts.1 & 0x00ff_ffff_ffff_ffff
  let count = Int((rawGuts.1 &>> 56) & 0x0f)
  // Handle sign.
  // "0"..."9" == 0x30...0x39
  // "-" == 0x2d
  // "+" == 0x2b
  var hasMinus = false
  let first = word1 & 0xff
  if first < 0x30 { // Plus, minus or an invalid character.
    guard _fastPath(count > 1), // Disallow "-"/"+" without any digits.
      _fastPath(Result.isSigned && first == _ascii("-"))
      || _fastPath(first == _ascii("+"))
      else { return nil }
    hasMinus = _fastPath(first == _ascii("-"))
    word1 = (word1 ^ first) | 0x30 // Clear first char and add "0" character.
  } else {
    guard _fastPath(count > 0) else { return nil }
  }
  // Choose specialization based on radix (normally branch is optimized away).
  let result_: UInt64?
  switch radix {
  case 10: result_ = _parseBase10Unsigned(from: (word1, word2), count: count)
  case 16: result_ = _parseHexUnsigned(from: (word1, word2), count: count)
  case 2: result_ = _parseBinaryUnsigned(from: (word1, word2), count: count)
  default:
    var raw = (word1.littleEndian, word2.littleEndian)
    result_ = withUnsafeBytes(of: &raw) { rawBufPtr -> UInt64? in
      let start = rawBufPtr.baseAddress._unsafelyUnwrappedUnchecked
        .assumingMemoryBound(to: UInt8.self)
      let ptr = UnsafeBufferPointer(start: start, count: count)
      var utf8 = ptr.makeIterator()
      let first = utf8.next()._unsafelyUnwrappedUnchecked
      return _parseFromUTF8Unsigned(first: first, rest: &utf8, radix: radix)
    }
  }
  guard _fastPath(result_ != nil), var result = result_ else { return nil }
  // Apply sign & check limits.
  // Note: This assumes Result is stored as two's complement,
  //   which is already assumed elsewhere in the stdlib.
  let max = Result.max.magnitude &+ (hasMinus ? 1 : 0)
  guard _fastPath(result <= max) else { return nil }
  if hasMinus { result = 0 &- result }
  // Or ensure the compiler generates a conditional negate.
  return Result(truncatingIfNeeded: result)
}

@inlinable @inline(__always)
internal func _parseBase10Unsigned(
  from rawGuts: _StringObject.RawBitPattern, count: Int
) -> UInt64? {
  let (word1, word2) = rawGuts
  // Note: We parse base 10 in 4-byte chunks.
  // Functions.
  func convertToDigits(_ word: UInt64, bitCount: Int) -> UInt64? {
    let shift = (64 &- bitCount) // bitCount must be >0.
    // Convert characters to digits.
    var digits = word &- 0x3030_3030_3030_3030
    // Align digits to big end and shift out garbage.
    digits &<<= shift
    // Check limits.
    let hasBelow0 = digits // Underflow causes at least one bit to be set.
    let hasAbove9 = digits &+ (0x7f - 9) &* 0x0101_0101_0101_0101
    guard _fastPath((hasBelow0 | hasAbove9) & 0x8080_8080_8080_8080 == 0)
      else { return nil }
    return digits
  }
  func parseDigitChunk(_ chunk32: UInt32) -> UInt64 {
    // We now have 0x0s0r_0q0p,
    // where p is the first character thus highest value (1000s' place).
    var chunk = UInt64(chunk32)
    chunk |= (chunk &<< 24)
    chunk &= 0x000f_000f_000f_000f
    // Due to the above we now have 0x000s_000q_000r_000p.
    // Multiplying with the 'magic' number 0x03e8_000a_0064_0001,
    // we effectively take the sum of the multiplications below:
    // 0x000s_000q_000r_000p * 1
    // 0x000r_000p_0000_0000 * 10 (0xa)
    // 0x000q_000r_000p_0000 * 100 (0x64)
    // 0x000p_0000_0000_0000 * 1000 (0x3e8)
    // ------------------------------------ +
    // The top 4 nibbles will now contain the parsed value. The less-significant
    // bits will never affect those bits since 0x000r * 100 is always < 0x1_000.
    chunk &*= 0x03e8_000a_0064_0001
    chunk &>>= 48
    return chunk
  }
  // Main.
  let bitCount = count &* 8
  if bitCount <= 32 { // 1 chunk case.
    let w_ = convertToDigits(word1, bitCount: bitCount)
    guard _fastPath(w_ != nil), let w = w_ else { return nil }
    return parseDigitChunk(UInt32(w &>> 32))
  } else {
    let word1BitCount = bitCount % 64
    // Ok, so normally digitCount should be >0 but atm it handles that
    // as if it where 8 so that still actually checks out for our case above.
    let w1_ = convertToDigits(word1, bitCount: word1BitCount)
    guard _fastPath(w1_ != nil), let w1 = w1_ else { return nil }
    var result = parseDigitChunk(UInt32(truncatingIfNeeded: w1))
    result &*= 10_000
    result &+= parseDigitChunk(UInt32(w1 &>> 32))
    // 2-word case.
    if bitCount > 64 {
      let shift = (64 &- word1BitCount) // 0 < shift < 64.
      let word2 = (word2 &<< shift) | (word1 &>> (64 &- shift))
      let w2_ = convertToDigits(word2, bitCount: 64)
      guard _fastPath(w2_ != nil), let w2 = w2_ else { return nil }
      result &*= 10_000
      result &+= parseDigitChunk(UInt32(truncatingIfNeeded: w2))
      result &*= 10_000
      result &+= parseDigitChunk(UInt32(w2 &>> 32))
    }
    return result
  }
}

@inlinable @inline(__always)
internal func _parseHexUnsigned(
  from rawGuts: _StringObject.RawBitPattern, count: Int
) -> UInt64? {
  let (word1, word2) = rawGuts
  func parseChunk(chunk: UInt64, bitCount: Int) -> UInt64? {
    let shift = 64 &- bitCount // bitCount must be >0.
    // "0"..."9" == 0x30...0x39
    // "A"..."Z" == 0x41...0x5A
    // "a"..."z" == 0x61...0x7A
    var chunk = MiniSIMD8(storage: chunk) // Can have overflow due to non-ascii.
    var invalid = chunk.flags
    let letterFlags = chunk .> _ascii("9")
    let letterMask = letterFlags.valueMask
    // Make letters uppercase (zero bit 5).
    chunk = chunk & ~(letterMask & 0x20)
    // Move "A" to just above "9".
    invalid = invalid | ((chunk .< _ascii("A")) & letterFlags)
    let offset = _ascii("A") - (_ascii("9") + 1)
    var digits = chunk &- (letterMask & offset)
    // Convert characters to digits.
    var baseline = MiniSIMD8(repeating: _ascii("0"))
    baseline.storage &>>= shift
    digits = digits &- baseline // Might have underflow.
    // Align digits to big end.
    digits.storage &<<= shift
    guard (digits | invalid.bits).areAllHex else { return nil }
    // Turn the digits into a single value.
    return digits.extractLowNibblesLittleEndian()
  }
  // Main.
  let bitCount = count &* 8
  if bitCount <= 64 {
    return parseChunk(chunk: word1, bitCount: bitCount)
  } else {
    let value1_ = parseChunk(chunk: word1, bitCount: 64)
    guard _fastPath(value1_ != nil), let value1 = value1_ else { return nil }
    let word2BitCount = bitCount &- 64
    var result = value1 &<< (word2BitCount / 2)
    let value2_ = parseChunk(chunk: word2, bitCount: word2BitCount)
    guard _fastPath(value2_ != nil), let value2 = value2_ else { return nil }
    result |= value2
    return result
  }
}

@inlinable @inline(__always)
internal func _parseBinaryUnsigned(
  from rawGuts: _StringObject.RawBitPattern, count: Int
) -> UInt64? {
  let (word1, word2) = rawGuts
  func parseChunk(chunk: UInt64, bitCount: Int) -> UInt64? {
    let shift = 64 &- bitCount // bitCount must be >0.
    // Convert characters to digits.
    var digits = chunk &- 0x3030_3030_3030_3030
    // Align digits to big end and shift out garbage.
    digits &<<= shift
    // The following check is enough, even if the original value overflowed.
    guard _fastPath(digits & ~0x0101_0101_0101_0101 == 0) else { return nil }
    // Turn the digits into a single value.
    return (digits &* 0x8040_2010_0804_0201) &>> 56
  }
  // Main.
  let bitCount = count &* 8
  if bitCount <= 64 {
    return parseChunk(chunk: word1, bitCount: bitCount)
  } else {
    let value1_ = parseChunk(chunk: word1, bitCount: 64)
    guard _fastPath(value1_ != nil), let value1 = value1_ else { return nil }
    let word2BitCount = bitCount &- 64
    var result = value1 &<< (word2BitCount/8)
    let value2_ = parseChunk(chunk: word2, bitCount: word2BitCount)
    guard _fastPath(value2_ != nil), let value2 = value2_ else { return nil }
    result |= value2
    return result
  }
}

@inlinable
internal func _parseFromUTF8<
  Iterator : IteratorProtocol, Result : FixedWidthInteger
>(_ utf8: inout Iterator, radix: Int) -> Result?
where Iterator.Element == UInt8 {
  return _parseFromUTF8Inlined(&utf8, radix: radix)
}

@inlinable @inline(__always)
internal func _parseFromUTF8Inlined<
  Iterator : IteratorProtocol, Result : FixedWidthInteger
>(_ utf8: inout Iterator, radix: Int) -> Result?
where Iterator.Element == UInt8 {
  typealias UResult = Result.Magnitude
  guard _fastPath(UResult(exactly: radix) != nil) else {
    preconditionFailure("Result.Magnitude must be able to represent the radix")
  }
  // Get first character.
  let first_ = utf8.next()
  guard _fastPath(first_ != nil), var first = first_ else { return nil }
  // Handle sign.
  let hasMinus: Bool
  if first < _ascii("0") { // Both "+" and "-" are < any digit/letter.
    guard _fastPath(Result.isSigned && first == _ascii("-"))
      || _fastPath(first == _ascii("+")) else { return nil }
    hasMinus = (first == _ascii("-"))
    // Get a new first character.
    let second_ = utf8.next()
    guard _fastPath(second_ != nil), let second = second_ else { return nil }
    first = second
  } else {
    hasMinus = false
  }
  // Parse value.
  let result_: UResult?
    = _parseFromUTF8Unsigned(first: first, rest: &utf8, radix: radix)
  guard _fastPath(result_ != nil), var result = result_ else { return nil }
  // Apply sign & check limits.
  let max = Result.max.magnitude &+ (hasMinus ? 1 : 0)
  guard _fastPath(result <= max) else { return nil }
  if hasMinus { result = 0 &- result }
  return Result(truncatingIfNeeded: result)
}

@inlinable @inline(__always)
internal func _parseFromUTF8Unsigned<
  Iterator : IteratorProtocol, Result : FixedWidthInteger
>(first: UInt8, rest utf8: inout Iterator, radix: Int) -> Result?
where Iterator.Element == UInt8, Result : UnsignedInteger {
  let result_: Result? = _parseCodeUnit(first, radix: radix)
  guard _fastPath(result_ != nil), var result = result_ else { return nil }
  while let cu = utf8.next() {
    let digit_: Result? = _parseCodeUnit(cu, radix: radix)
    guard _fastPath(digit_ != nil), let digit = digit_ else { return nil }
    // Add digit: result = result * radix + digit.
    let overflow1, overflow2: Bool
    (result, overflow1) = result.multipliedReportingOverflow(by: Result(radix))
    (result, overflow2) = result.addingReportingOverflow(digit)
    guard _fastPath(!overflow1 && !overflow2) else { return nil }
  }
  return result
}

@inlinable @inline(__always)
internal func _parseCodeUnit<Result : FixedWidthInteger>(
  _ cu: UInt8, radix: Int
) -> Result? {
  var digit = cu &- _ascii("0")
  if radix > 10 && digit > 10 {
    digit = (cu & ~0x20) &- _ascii("A") &+ 10 // Clear bit 5 to uppercase.
  }
  // We only need to check the upper bound as we're using a UInt8.
  guard _fastPath(digit < radix) else { return nil }
  return Result(truncatingIfNeeded: digit)
}

@inlinable @inline(__always)
internal func _ascii(_ c: Unicode.Scalar) -> UTF8.CodeUnit {
  return UTF8.CodeUnit(c.value)
}







/// Stores eight 7-bit unsigned integers in the bytes of a UInt64.
///
/// Primary use is for operating on ASCII/UTF8 with up to 8 characters at the same time.
/// Notes:
/// - On overflow or underflow in any lanes, all values are generally invalid.
///   However, the flag bits are still meaningful. For overflow, the flags bits
///   represent overflow per lane. In case of underflow, the individual flag
///   bits are not meaningful but at least one of them is guaranteed to be set.
/// - Any scalar arguments must also be 7-bit.
@usableFromInline @frozen
internal struct MiniSIMD8 : Hashable, CustomStringConvertible {
  @usableFromInline var storage: UInt64

  @inlinable init(storage: UInt64) { self.storage = storage }
  @inlinable init(repeating value: UInt8) {
    storage = UInt64(value) &* 0x0101_0101_0101_0101
  }

  @inlinable static var zero: MiniSIMD8 { return MiniSIMD8(repeating: 0) }
  @inlinable var flags: Flags { return Flags(self) }

  /// Whether all lanes are 0 or 1 and have no overflow.
  @inlinable var areAllBinary: Bool { return self & ~0x01 == .zero }
  /// Whether all lanes are <= 16 and have no overflow.
  @inlinable var areAllHex: Bool { return self & ~0x0f == .zero  }

  /// Extract lowest bit from each lane into one byte, preserving their current order in memory.
  @inlinable func extractLowBitsFromMemoryOrder() -> UInt8 {
    let m: UInt64 = (1.littleEndian == 1) ? 0x8040_2010_0804_0201 : 0x0102_0408_1020_4080
    return UInt8(truncatingIfNeeded: (storage &* m) &>> 56)
  }

  @inlinable func extractLowBitsLittleEndian() -> UInt8 {
    return UInt8(truncatingIfNeeded: (storage &* 0x8040_2010_0804_0201) &>> 56)
  }

  @inlinable func extractLowNibblesFromMemoryOrder() -> UInt64 {
    // Basically just a single PEXT instruction, though LLVM doesn't generate that at the moment.
    if 1.littleEndian == 1 {
      return extractLowNibblesLittleEndian()
    } else { // 0x0p0q_0r0s_0t0u_0v0w => 0x0000_0000_pqrs_tuvw
      var x = storage
      x = (x | x &>> 4)  & 0x00ff_00ff_00ff_00ff // 0x00pq_00rs_00tu_00vw
      x = (x | x &>> 8)  & 0x0000_ffff_0000_ffff // 0x0000_pqrs_0000_tuvw
      x = (x | x &>> 16) & 0x0000_0000_ffff_ffff // 0x0000_0000_pqrs_tuvw
      return x
    }
  }

  @inlinable func extractLowNibblesLittleEndian() -> UInt64 {
    // Basically just a single PEXT instruction, though LLVM doesn't generate that at the moment.
    var x = storage
    // 0x0p0q_0r0s_0t0u_0v0w => 0x0000_0000_wvut_srqp
    x = (x | x &<< 12) & 0xff00_ff00_ff00_ff00 // 0xqp00_sr00_ut00_wv00
    x = (x | x &>> 24) & 0x0000_ffff_0000_ffff // 0x0000_srqp_0000_wvut
    x = (x &<< 16 | x &>> 32) & 0xffff_ffff    // 0x0000_0000_wvut_srqp
    return x
  }

  @usableFromInline typealias Mask = MiniSIMD8

  @usableFromInline @frozen
  struct Flags : Equatable, CustomStringConvertible {
    // Unsanitized, all non flag bits are garbage
    @usableFromInline var rawBits: MiniSIMD8

    @inlinable var bits: MiniSIMD8 { return (rawBits & 0x80) }
    @inlinable var isAnySet: Bool { return bits != .zero }
    @inlinable var areAllSet: Bool { return bits == MiniSIMD8(repeating: 0x80) }

    @inlinable var valueMask: Mask {
      return bits &- MiniSIMD8(storage: bits.storage &>> 7)
    }

    @inlinable init(_ storage: MiniSIMD8) { self.rawBits = storage }

    @inlinable static prefix func ~(x: Flags) -> Flags { return Flags(~x.rawBits) }
    @inlinable static func |(lhs: Flags, rhs: Flags) -> Flags { return Flags(lhs.rawBits | rhs.rawBits) }
    @inlinable static func &(lhs: Flags, rhs: Flags) -> Flags { return Flags(lhs.rawBits & rhs.rawBits) }

    @inlinable var description: String {
      let values = (0..<8).map { ((rawBits.storage >> ($0*8)) & 0x01).description }.joined(separator: ", ")
      return "MiniSIMD8.Flags(\(values))"
    }
  }

  @inlinable static prefix func ~(x: MiniSIMD8) -> MiniSIMD8 {
    return MiniSIMD8(storage: ~x.storage)
  }

  @inlinable static func &(lhs: MiniSIMD8, rhs: MiniSIMD8) -> MiniSIMD8 {
    return MiniSIMD8(storage: lhs.storage & rhs.storage)
  }

  @inlinable static func &(lhs: MiniSIMD8, rhs: UInt8) -> MiniSIMD8 {
    return lhs & MiniSIMD8(repeating: rhs)
  }

  @inlinable static func |(lhs: MiniSIMD8, rhs: MiniSIMD8) -> MiniSIMD8 {
    return MiniSIMD8(storage: lhs.storage | rhs.storage)
  }

  @inlinable static func |(lhs: MiniSIMD8, rhs: UInt8) -> MiniSIMD8 {
    return lhs | MiniSIMD8(repeating: rhs)
  }

  @inlinable static func ^(lhs: MiniSIMD8, rhs: MiniSIMD8) -> MiniSIMD8 {
    return MiniSIMD8(storage: lhs.storage ^ rhs.storage)
  }

  @inlinable static func ^(lhs: MiniSIMD8, rhs: UInt8) -> MiniSIMD8 {
    return lhs ^ MiniSIMD8(repeating: rhs)
  }

  @inlinable static func &+(lhs: MiniSIMD8, rhs: MiniSIMD8) -> MiniSIMD8 {
    return MiniSIMD8(storage: lhs.storage &+ rhs.storage)
  }

  @inlinable static func &+(lhs: MiniSIMD8, rhs: UInt8) -> MiniSIMD8 {
    return lhs &+ MiniSIMD8(repeating: rhs)
  }

  @inlinable static func &+(lhs: UInt8, rhs: MiniSIMD8) -> MiniSIMD8 {
    return MiniSIMD8(repeating: lhs) &+ rhs
  }

  @inlinable static func &-(lhs: MiniSIMD8, rhs: MiniSIMD8) -> MiniSIMD8 {
    return MiniSIMD8(storage: lhs.storage &- rhs.storage)
  }

  @inlinable static func &-(lhs: MiniSIMD8, rhs: UInt8) -> MiniSIMD8 {
    return lhs &- MiniSIMD8(repeating: rhs)
  }

  @inlinable static func &-(lhs: UInt8, rhs: MiniSIMD8) -> MiniSIMD8 {
    return MiniSIMD8(repeating: lhs) &- rhs
  }

  // Pointwise comparisons
  @inlinable static func .>(lhs: MiniSIMD8, rhs: UInt8) -> Flags { return Flags(lhs &+ (0x7f &- rhs)) }
  @inlinable static func .>=(lhs: MiniSIMD8, rhs: UInt8) -> Flags { return Flags(lhs &+ (0x80 &- rhs)) }
  @inlinable static func .<(lhs: MiniSIMD8, rhs: UInt8) -> Flags { return Flags((0x7f &+ rhs) &- lhs) }
  @inlinable static func .<=(lhs: MiniSIMD8, rhs: UInt8) -> Flags { return Flags((0x80 &+ rhs) &- lhs) }
  @inlinable static func .==(lhs: MiniSIMD8, rhs: UInt8) -> Flags { return Flags(((lhs ^ ~rhs) & 0x7f) &+ 1) }

  @inlinable var description: String {
    let values = (0..<8).map { ((storage >> ($0*8)) & 0xff).description }.joined(separator: ", ")
    return "MiniSIMD8(\(values))"
  }
}

