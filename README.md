An (unfinished) arbitrary precision big number library for [zig](http://ziglang.org/).

The interface is akin to that of GMP.

```
const std = @import("std");

const bn = @import("bn.zig");
const Bn = bn.BnWithAllocator(&std.debug.global_allocator);

pub fn main() -> %void {
    var a = %%Bn.init();
    defer a.deinit();
    var b = %%Bn.init();
    defer b.deinit();

    %%a.setStr(10, "1990273423429836742364234234234");
    %%b.setStr(10, "1990273423429836742364234234234");

    %%bn.add(&a, &a, &b);

    var result = %%a.toStr();
    defer result.deinit();
    %%std.io.stdout.printf("{}\n", result);
}
```
