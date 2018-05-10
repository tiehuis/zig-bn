To run all measurements:

```
make run
```

## Notes

Go and C use assembly functions for their low-level details which is where they
get the majority of their performance from. Zig and Rust do not, Python uses C
for its implementation.

We use base-case multiplcation for the factorial test. This is the reason why
we are the slowest here (although only just!).

The hex printing to verify the results has negigible runtime. This a simple
iteration over all limbs in all these implementations.

## Measurements

Using 64-bit limbs on zig.

```
$ make run-fib
------ fibonacci (lladd, llsub) 
fib-zig: 0:00.35 real, 0.34 user, 0.00 sys
0d569dee4b1a3483666d82ba239745c8  -
  debug: 0:02.06 real, 2.05 user, 0.00 sys
0d569dee4b1a3483666d82ba239745c8  -

fib-c:   0:00.18 real, 0.18 user, 0.00 sys
0d569dee4b1a3483666d82ba239745c8  -

fib-go:  0:00.22 real, 0.21 user, 0.00 sys
0d569dee4b1a3483666d82ba239745c8  -

fib-py:  0:00.83 real, 0.82 user, 0.00 sys
0d569dee4b1a3483666d82ba239745c8  -

fib-rs:  0:00.87 real, 0.86 user, 0.00 sys
0d569dee4b1a3483666d82ba239745c8  -
```

```
$ make run-fac
------ factorial (llmul, lladd) 
fac-zig: 0:00.56 real, 0.56 user, 0.00 sys
18ef33d21ad1dc05a899112e6de5270f  -

fac-c:   0:00.19 real, 0.19 user, 0.00 sys
18ef33d21ad1dc05a899112e6de5270f  -

fac-go:  0:00.21 real, 0.21 user, 0.00 sys
18ef33d21ad1dc05a899112e6de5270f  -

fac-py:  0:00.52 real, 0.50 user, 0.01 sys
18ef33d21ad1dc05a899112e6de5270f  -

fac-rs:  0:00.55 real, 0.54 user, 0.00 sys
18ef33d21ad1dc05a899112e6de5270f  -

```

```
$ make system

Architecture:        x86_64
CPU op-mode(s):      32-bit, 64-bit
Byte Order:          Little Endian
CPU(s):              4
On-line CPU(s) list: 0-3
Thread(s) per core:  1
Core(s) per socket:  4
Socket(s):           1
NUMA node(s):        1
Vendor ID:           GenuineIntel
CPU family:          6
Model:               94
Model name:          Intel(R) Core(TM) i5-6500 CPU @ 3.20GHz
Stepping:            3
CPU MHz:             3334.836
CPU max MHz:         3600.0000
CPU min MHz:         800.0000
BogoMIPS:            6386.00
Virtualization:      VT-x
L1d cache:           32K
L1i cache:           32K
L2 cache:            256K
L3 cache:            6144K
NUMA node0 CPU(s):   0-3
Flags:               fpu vme de pse tsc msr pae mce cx8 apic sep mtrr pge mca cmov pat pse36 clflush dts acpi mmx fxsr sse sse2 ss ht tm pbe syscall nx pdpe1gb rdtscp lm constant_tsc art arch_perfmon pebs bts rep_good nopl xtopology nonstop_tsc cpuid aperfmperf tsc_known_freq pni pclmulqdq dtes64 monitor ds_cpl vmx smx est tm2 ssse3 sdbg fma cx16 xtpr pdcm pcid sse4_1 sse4_2 x2apic movbe popcnt tsc_deadline_timer aes xsave avx f16c rdrand lahf_lm abm 3dnowprefetch cpuid_fault invpcid_single pti tpr_shadow vnmi flexpriority ept vpid fsgsbase tsc_adjust bmi1 hle avx2 smep bmi2 erms invpcid rtm mpx rdseed adx smap clflushopt intel_pt xsaveopt xsavec xgetbv1 xsaves ibpb ibrs stibp dtherm ida arat pln pts hwp hwp_notify hwp_act_window hwp_epp

zig:  0.2.0.ef3111be
gcc:  gcc (GCC) 8.1.0
go:   go version go1.10.2 linux/amd64
py:   Python 3.6.5
rust: rustc 1.25.0 (84203cac6 2018-03-25)
```
