# ZeroSpec

## Build

### Dependencies

To build ZeroSpec, you need the following dependencies installed:

- LLVM 19.1.7
- CMake >= 3.20
- GCC 12.3.0
- vcpkg

### Build & Install

```
git clone
cd sparse-passes
export VCPKG_ROOT=/path/to/vcpkg_root
export LLVM_INSTALL_PREFIX=/path/to/llvm
cmake -B build --preset release
cmake --build build
```

Load the environment to use the installed ZeroSpec:

```
source env.sh
```

### How to use ZeroSpec
To use ZeroSpec, you need to complete each step of the **Build & Install**

ZeroSpec is implemented as Out-of-tree (builds against a binary LLVM installation (no need to build LLVM from sources)) passes, so we can run it with opt or clang.

We provide some wrapper scripts to run the pass. You can simply replace clang with clang.sh and replace clang++ with clang++.sh
Usage:

```
ZERO_SPEC_MODE=DETECT clang++.sh <args-for-clang> 
```

If environment variable `ZERO_SPEC_MODE` is not set, clang.sh will work as original clang without running ZeroSpec.

After instrumentation, you can run the app, and zero information about the app will be dumped. 
If ZERO_SPEC_LOG_PATH is not set, the data will be saved in current directory.

```
ZERO_SPEC_LOG_PATH=<path> <run_app>
```

Now we have the zero information, use sparse_report.py to process it, and you can get a zero.report.

```
sparse_report.py <path-to-log-path>/data-<pid>
```

Finally, optimize the app with zero information:

```
ZERO_SPEC_MODE=OPT ZERO_SPEC_DB=<path-to-zero.report> clang_wrapper.py <args>
```



### How to use ZeroSpec in CMake projects
Usage:
```
# at project build path
cmake -DCMAKE_C_COMPILER=clang.sh -DCMAKE_CXX_COMPILER=clang++.sh <project-path>
ZERO_SPEC_MODE=DETECT make -j
<run instrumented target app>
cd <ZERO_SPEC_LOG_PATH>
sparse_report.py # sparse_report.py will find the newest data-xxx and generate zero.report at current directory
cd <project-build-path>
make clean
ZERO_SPEC_MODE=OPT ZERO_SPEC_DB=<path-to-zero.report> make -j 
<run optimized target app>
```


## ZeroSpec Docker Image

This repository provides Dockerfiles for building the ZeroSpec project image on different architectures.

### Available Architectures

* `x86`
* `aarch64`

### Build Instructions

To build the Docker image for your target architecture, run the following command from the root of the repository:

```bash
docker build -f dockerfiles/<arch>/dockerfile -t zerospec:<arch> .
```

