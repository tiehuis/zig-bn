const bn = @import("bn.zig");
const Limb = bn.Limb;
const DoubleLimb = bn.DoubleLimb;
const assert = @import("std").debug.assert;

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

// a + b * c + carry
//
// Carry is set to resulting overflow value.
pub fn muladdLimbWithCarry(a: Limb, b: Limb, c: Limb, carry: &Limb) -> Limb {
    const result = DoubleLimb(a) + DoubleLimb(b) * DoubleLimb(c) + DoubleLimb(*carry);
    *carry = @truncate(Limb, result >> 8 * @sizeOf(Limb));
    @truncate(Limb, result)
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

test "ll.addLimbWithCarry" {
    var a: Limb = 3;
    var b: Limb = @maxValue(Limb);
    var c: Limb = 7;
    var d = addLimbWithCarry(a, b, &c);

    assert(c == 1);
    assert(d == 9);
}

test "ll.subLimbWithBorrow" {
    var a: Limb = 5;
    var b: Limb = 4;
    var c: Limb = 3;
    var d = subLimbWithBorrow(a, b, &c);

    assert(c == 1);
    assert(d == @maxValue(Limb) - 1);
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
        div2LimbByLimb(&q[index], r, *r, a[index], b);
    }
}

pub fn add3(dst: []Limb, a: []const Limb, b: []const Limb) {
    assert(a.len >= b.len);
    assert(dst.len >= a.len + 1);

    var carry: Limb = 0;
    for (b) |_, i| {
        dst[i] = addLimbWithCarry(a[i], b[i], &carry);
    }

    // Propagate carry across remaining a limbs
    for (a[b.len..]) |d, i| {
        dst[i] = addLimbWithCarry(a[i], 0, &carry);
        if (carry == 0) {
            break;
        }
    }
    if (carry != 0) {
        dst[a.len] = carry;
        carry = 0;
    }

    assert(carry == 0);
}

// Assumes a, b >= 0 and a >= b
pub fn sub3(dst: []Limb, a: []const Limb, b: []const Limb) {
    assert(a.len >= b.len);
    assert(dst.len >= b.len);

    var borrow: Limb = 0;
    for (b) |_, i| {
        dst[i] = subLimbWithBorrow(a[i], b[i], &borrow);
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
        dst[i] += muladdLimbWithCarry(dst[i], a[i], b, &carry);
    }

    if (carry != 0) {
        dst[a.len] = muladdLimbWithCarry(dst[a.len], 0, b, &carry);
    }
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
        muladd3Line(dst[i..], a, b[i]);
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
