const std = @import("std");
const bn = @import("bn.zig");
const Limb = bn.Limb;
const DoubleLimb = bn.DoubleLimb;
const assert = std.debug.assert;

/// Low-level operations on single limbs.
///
/// These are heavily executed and are worth optimizing in assembly.

// a + b + carry
//
// Carry is set to resulting overflow value.
pub fn addLimbWithCarry(a: Limb, b: Limb, carry: &Limb) -> Limb {
    const result = DoubleLimb(a) + DoubleLimb(b) + DoubleLimb(*carry);
    *carry = @truncate(Limb, result >> 8 * @sizeOf(Limb));
    @truncate(Limb, result)
}

test "ll.addLimbWithCarry" {
    var a: Limb = 0xFFFFFFFF;
    var b: Limb = 0xFFFFFFFF;
    var c: Limb = 0;
    var r: Limb = undefined;

    r = addLimbWithCarry(a, b, &c);
    assert(r == 0xFFFFFFFE);
    assert(c == 0x1);

    c = 17;
    r = addLimbWithCarry(2, 0, &c);
    assert(r == 19);
    assert(c == 0);
}

// a + b * c + carry
//
// Carry is set to resulting overflow value.
pub fn muladdLimbWithCarry(a: Limb, b: Limb, c: Limb, carry: &Limb) -> Limb {
    const result = DoubleLimb(a) + DoubleLimb(b) * DoubleLimb(c) + DoubleLimb(*carry);
    *carry = @truncate(Limb, result >> 8 * @sizeOf(Limb));
    @truncate(Limb, result)
}

test "ll.muladdLimbWithCarry" {
    var a: Limb = 0xFFFFFFFF;
    var b: Limb = 0xFFFFFFFF;
    var c: Limb = 0xFFFFFFFF;
    var d: Limb = 1;
    var r: Limb = undefined;

    r = muladdLimbWithCarry(a, b, c, &d);
    assert(r == 0x1);
    assert(d == 0xFFFFFFFF);

    d = 17;
    r = muladdLimbWithCarry(10, 0, 7, &d);
    assert(r == 27);
    assert(d == 0);
}

// a - b + borrow
//
// Carry is set to resulting underflow value.
pub fn subLimbWithBorrow(a: Limb, b: Limb, borrow: &Limb) -> Limb {
    const base = DoubleLimb(1) << 8 * @sizeOf(Limb);
    const result = base + DoubleLimb(a) - DoubleLimb(b) - DoubleLimb(*borrow);
    const hi = @truncate(Limb, result >> 8 * @sizeOf(Limb));
    *borrow = Limb(hi == 0);
    @truncate(Limb, result)
}

test "ll.subLimbWithBorrow" {
    var a: Limb = 5;
    var b: Limb = 4;
    var c: Limb = 3;
    var d = subLimbWithBorrow(a, b, &c);

    assert(c == 1);
    assert(d == @maxValue(Limb) - 1);
}

// Divide a double sized Limb by a single Limb divisor.
//
// The quotient and remainder are stored in specified out variables.
// TODO: Tuples would be nice to have for something like this.
pub fn div2LimbByLimb(q: &Limb, r: &Limb, hi: Limb, lo: Limb, d: Limb) {
    assert(hi < d);

    const lhs = (DoubleLimb(hi) << 8 * @sizeOf(Limb)) | (DoubleLimb(lo));
    const rhs = DoubleLimb(d);
    *q = Limb(lhs / rhs);
    *r = Limb(lhs % rhs);
}

/// Higher-level functions based on primitives which work on limb arrays.
///
/// These typically expect memory to be preallocated to correct sizes and make assumptions about
/// the length of inputs relative to one another.

// a / b where b is a single limb.
pub fn divRemSingle(q: []Limb, r: &Limb, a: []const Limb, b: Limb) {
    assert(q.len >= a.len);
    *r = 0;

    for (a) |_, i| {
        const index = a.len - i - 1;

        // This does not handle the special case where a < b
        @inlineCall(div2LimbByLimb, &q[index], r, *r, a[index], b);
    }
}

test "ll.divRemSingle" {
    var q: [2]Limb = undefined;
    var r: Limb = undefined;

    var a: [2]Limb = undefined;
    var b: Limb = undefined;

    a[1] = 0;
    a[0] = 4;
    b = 2;
    divRemSingle(q[0..2], &r, a[0..2], b);
    assert(q[1] == 0);
    assert(q[0] == 2);
    assert(r == 0);

    a[1] = 0;
    a[0] = 987;
    b = 13;
    divRemSingle(q[0..2], &r, a[0..2], b);
    assert(q[1] == 0);
    assert(q[0] == 75);
    assert(r == 12);

    // 240530240918 / 324 = 742377286 r 254
    a[1] = 56;
    a[0] = 12072342;
    b = 324;
    divRemSingle(q[0..2], &r, a[0..2], b);
    assert(q[1] == 0);
    assert(q[0] == 742377286);
    assert(r == 254);
}

pub fn add3(dst: []Limb, a: []const Limb, b: []const Limb) {
    assert(a.len >= b.len);
    assert(dst.len >= a.len + 1);

    var carry: Limb = 0;
    var i: usize = 0;

    while (i < b.len) : (i += 1) {
        dst[i] = @inlineCall(addLimbWithCarry, a[i], b[i], &carry);
    }

    while (i < a.len) : (i += 1) {
        dst[i] = @inlineCall(addLimbWithCarry, a[i], 0, &carry);
        if (carry == 0) {
            break;
        }
    }

    if (carry != 0) {
        dst[i] = carry;
        carry = 0;
    }

    assert(carry == 0);
}

test "ll.add3 single" {
    var dst: [2]Limb = undefined;
    var a: [1]Limb = undefined;
    var b: [1]Limb = undefined;

    a[0] = 5;
    b[0] = 4;
    add3(dst[0..], a[0..], b[0..]);
    assert(dst[0] == 9);

    a[0] = 0xFFFFFFF7;
    b[0] = 1237;
    add3(dst[0..], a[0..], b[0..]);
    assert(dst[0] == 0x4CC);
    assert(dst[1] == 0x1);

    a[0] = 0x102;
    b[0] = 0;
    add3(dst[0..], a[0..], b[0..]);
    assert(dst[0] == 0x102);
}

test "ll.add3 multi" {
    var dst: [3]Limb = undefined;
    var a: [2]Limb = undefined;
    var b: [1]Limb = undefined;

    a[0] = 0xFFFFFFFF;
    a[1] = 0xFFFFFFFF;
    b[0] = 0;
    add3(dst[0..], a[0..], b[0..]);
    assert(dst[0] == 0xFFFFFFFF);
    assert(dst[1] == 0xFFFFFFFF);

    b[0] = 137;
    add3(dst[0..], a[0..], b[0..]);
    assert(dst[0] == 136);
    assert(dst[1] == 0);
    assert(dst[2] == 1);
}

// Assumes a, b >= 0 and a >= b
pub fn sub3(dst: []Limb, a: []const Limb, b: []const Limb) {
    assert(a.len >= b.len);
    assert(dst.len >= b.len);

    var borrow: Limb = 0;
    for (b) |_, i| {
        dst[i] = @inlineCall(subLimbWithBorrow, a[i], b[i], &borrow);
    }
}

// dst += a * b
//
// Perform a carrying multiplication spread into a limb slice. This can be thought of as a single
// pass over a multiplicative cross-product.
fn muladd3Line(dst: []Limb, a: []const Limb, b: Limb) {
    assert(dst.len >= a.len + 1);
    if (b == 0) {
        return;
    }

    var carry: Limb = 0;
    for (a) |_, i| {
        dst[i] = @inlineCall(muladdLimbWithCarry, dst[i], a[i], b, &carry);
    }

    if (carry != 0) {
        dst[a.len] = @inlineCall(muladdLimbWithCarry, dst[a.len], 0, b, &carry);
    }

    assert(carry == 0);
}

test "ll.muladd3Line" {
    var dst: [3]Limb = undefined;
    var a: [2]Limb = undefined;
    var b: Limb = undefined;

    dst[0] = 0xF0000000;
    dst[1] = 0xE0000000;
    dst[2] = 0xD0000000;
    a[0] = 0xFFFFFFFF;
    a[1] = 0xEEEEEEEE;
    b = 2;

    muladd3Line(dst[0..], a[0..], b);
    assert(dst[0] == 0xEFFFFFFE);
    assert(dst[1] == 0xBDDDDDDE);
    assert(dst[2] == 0xD0000002);
}

// dst must not alias either a or b.
// a and b can alias one another.
pub fn muladd3(dst: []Limb, a: []const Limb, b: []const Limb) {
    assert(dst.len >= a.len + b.len + 1);
    assert(a.len >= b.len);

    // Basecase multiplication always.
    //
    // Prefer broadcasting over the longer limb input instead of the short to use the longest
    // cache-lines and minimize function calls.
    for (b) |_, i| {
        @inlineCall(muladd3Line, dst[i..], a, b[i]);
    }
}

test "ll.muladd3 single" {
    var dst: [3]Limb = undefined;
    var a: [1]Limb = undefined;
    var b: [1]Limb = undefined;

    dst[0] = 0x0F0F0F0F;
    dst[1] = 0;
    dst[2] = 0;
    a[0] = 1879;
    b[0] = 123091724;

    muladd3(dst[0..], a[0..], b[0..]);
    assert(dst[0] == 0xE8FA7423);
    assert(dst[1] == 0x35);
}

test "ll.muladd3 multi" {
    var dst: [5]Limb = undefined;
    var a: [2]Limb = undefined;
    var b: [2]Limb = undefined;

    dst[0] = 0xF0F0F0F0;
    dst[1] = 0xD0D0D0D0;
    dst[2] = 0xE0E0E0E0;
    dst[3] = 0xC0C0C0C0;
    a[0] = 0xFFEEDDCC;
    a[1] = 0x00112233;
    b[0] = 0x55778823;
    b[1] = 0xF000000E;

    muladd3(dst[0..], a[0..], b[0..]);
    assert(dst[0] == 0xAA41A3D4);
    assert(dst[1] == 0x568A86B9);
    assert(dst[2] == 0xA1C66803);
    assert(dst[3] == 0xC0D0D0D1);
}

/// Shift a left by n bits, storing the result in dst.
///
/// dst and a are allowed to alias.
pub fn shiftLeft(dst: []Limb, a: []const Limb, n: usize) {
    const sizeOfLimbBits = 8 * @sizeOf(Limb);

    // NOTE: Could reduce this further and not strictly require the extra leading limb.
    // Required for exact alias on non overflowing shift, unless we extend by 1 minimum limb above
    // which is an option.
    assert(dst.len >= a.len + n / sizeOfLimbBits);
    assert(dst.len >= 1 and a.len >= 1);

    const limb_shift = @divTrunc(n, sizeOfLimbBits) + 1;
    const sub_limb_shift = @rem(n, sizeOfLimbBits);

    // Iterate in reverse.
    var lo: Limb = 0;
    for (a) |_, ri| {
        const i = a.len - ri - 1;
        const nlo = std.math.shl(Limb, a[i], sub_limb_shift);
        dst[i + limb_shift] = std.math.shr(Limb, a[i], sizeOfLimbBits - sub_limb_shift) | lo;
        lo = nlo;
    }

    dst[limb_shift - 1] = lo;
    for (dst[0 .. limb_shift - 1]) |*b| {
        *b = 0;
    }
}

test "ll.shiftLeft" {
    var dst: [3]Limb = undefined;
    var a: [3]Limb = undefined;

    a[0] = 0xFFFFFFFF;
    shiftLeft(dst[0..], a[0..1], 0);
    assert(dst[0] == 0xFFFFFFFF);

    a[0] = 0xFFFFFFFF;
    a[1] = 0;
    shiftLeft(dst[0..], a[0..2], 1);
    assert(dst[0] == 0xFFFFFFFE);
    assert(dst[1] == 0x1);

    a[0] = 0xF0F0F0F0;
    a[1] = 0x0D0D0D0D;
    shiftLeft(dst[0..], a[0..2], 12);
    assert(dst[0] == 0x0F0F0000);
    assert(dst[1] == 0xD0D0DF0F);
    assert(dst[2] == 0x000000D0);

    dst[0] = 0x0FFFFFFF;
    shiftLeft(dst[0..], dst[0..1], 4);
    assert(dst[0] == 0xFFFFFFF0);
}

