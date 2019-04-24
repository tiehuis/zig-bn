**This is now merged into the [zig stdlib](https://github.com/ziglang/zig/tree/master/std/math/big)**.

An arbitrary precision big integer library for [zig](http://ziglang.org/).

The interface is akin to that of GMP.

```
const std = @import("std");
const ArenaAllocator = std.heap.ArenaAllocator;

const BigInt = @import("bigint.zig").BigInt;

pub fn main() !void {
    const arena = ArenaAllocator.init(std.debug.global_allocator);
    defer arena.deinit();
    var al = arena.allocator;

    var a = try BigInt.init(al);
    var b = try BigInt.init(al);

    try a.set(1990273423429836742364234234234);
    try b.set(1990273423429836742364234234234);

    try a.add(&a, &b);
    try a.mul(&a, &b);

    try a.mul(&a, 14343);
}
```
