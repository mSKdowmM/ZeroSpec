cmake_minimum_required(VERSION 3.4)
project(sparse-passes)

set(CMAKE_CXX_STANDARD 17)

set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -O2 -g")        #/MT
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -g -Wall -Wextra") 

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

find_package(Boost REQUIRED COMPONENTS graph)
find_package(fmt REQUIRED CONFIG)
get_target_property(Boost_graph_INTERFACE_INCLUDE_DIRECTORIES Boost::graph INTERFACE_INCLUDE_DIRECTORIES)
include_directories(${Boost_graph_INTERFACE_INCLUDE_DIRECTORIES})

if (DEVELOPING)
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DDEVELOPING")
endif()

# set(LLVM_PROJECT_DIR "/mnt/ssd2/dsk/sparse-compiler/llvm-project" )
# set(LLVM_BUILD_DIR "/mnt/ssd2/dsk/sparse-compiler/llvm-project/build-17" )
# set(LLVM_BUILD_DIR "/mnt/ssd2/dsk/llvm-17.0.0-debug")

# include_directories("${LLVM_PROJECT_DIR}/llvm/include")
if( LLVM_INSTALL_PREFIX STREQUAL "" )
	MESSAGE(FATAL_ERROR "LLVM_INSTALL_PREFIX is empty")
else()
	MESSAGE("LLVM_INSTALL_PREFIX=${LLVM_INSTALL_PREFIX}")
endif()

include_directories(SYSTEM "${LLVM_INSTALL_PREFIX}/include")
include_directories("./include")
link_directories("${LLVM_INSTALL_PREFIX}/lib")
# aux_source_directory(./src src_1)
# set(srcs ${src_1})
# add_compile_options(-fsanitize=address -fsanitize-recover=all -fsanitize=leak)

# add_link_options(-fsanitize=address -fsanitize-recover=all -fsanitize=leak)

# add_library(mypasses SHARED ${srcs})
add_library(DetectZero SHARED src/DetectZeroPass.cpp)
add_library(InstDestClassification SHARED src/InstDestClassification.cpp)
add_library(ZeroPGO SHARED src/ZeroPGOModulePass.cpp)
add_library(IfZeroOpt SHARED src/IfZeroOpt.cpp)
add_library(probe SHARED src/probe.cpp)
add_library(probe_helper SHARED src/probe_helper.cpp)
add_library(ZeroBenefitAnalysis SHARED src/ZeroBenefitAnalysis.cpp)
add_library(ZeroSpecOpt SHARED src/ZeroSpecOpt.cpp)
add_library(RemoveInstrumentations SHARED src/RemoveInstrumentations.cpp)
add_library(userop SHARED src/userop.cpp)

add_library(FunctionJIT SHARED src/FunctionJIT.cpp)

target_link_libraries(probe PRIVATE stdc++fs)
set_target_properties(probe PROPERTIES LINK_FLAGS "-static-libstdc++ -static-libgcc -fvisibility=hidden -fvisibility-inlines-hidden -Wl,--version-script=${PROJECT_SOURCE_DIR}/src/version.script")


target_link_libraries(DetectZero PUBLIC Boost::graph)
target_link_libraries(InstDestClassification PUBLIC Boost::graph)
target_link_libraries(ZeroBenefitAnalysis PUBLIC Boost::graph)
target_link_libraries(ZeroBenefitAnalysis PRIVATE probe_helper userop)
target_link_libraries(ZeroSpecOpt PUBLIC Boost::graph)
target_link_libraries(ZeroBenefitAnalysis PRIVATE FunctionJIT userop)


target_link_libraries(ZeroSpecOpt PRIVATE ZeroBenefitAnalysis)
target_link_libraries(ZeroSpecOpt PRIVATE probe_helper userop)
target_link_libraries(IfZeroOpt PRIVATE probe_helper)
target_link_libraries(DetectZero PUBLIC InstDestClassification fmt::fmt)
target_link_libraries(ZeroPGO PUBLIC DetectZero)
target_link_libraries(DetectZero PUBLIC ZeroBenefitAnalysis)

target_link_libraries(RemoveInstrumentations PRIVATE probe_helper)



if (DEVELOPING)
	MESSAGE("ENABLE DEVELOPING MODE")
	# add_library(LoopsInFunc SHARED src/LoopsInFuncPass.cpp)
	# add_library(LoopZeroUnswitch SHARED src/LoopZeroUnswitch.cpp)
	# target_link_libraries(LoopsInFunc PUBLIC LLVM-17rc)
endif()
# include_directories(./thirdparty/boost_1_81_0)


# if( LLVM_PROJECT_DIR STREQUAL "" )
# 	MESSAGE(FATAL_ERROR "LLVM_PROJECT_DIR is empty")
# else()
# 	MESSAGE("LLVM_PROJECT_DIR=${LLVM_PROJECT_DIR}")
# endif()

# set(mylibdir "${LLVM_PROJECT_DIR}/llvm/build/Release/lib")
# set(VTKLIBS LLVMCore LLVMSupport LLVMBinaryFormat LLVMRemarks LLVMBitstreamReader)
# foreach(libname ${VTKLIBS})
#         SET(FOUND_LIB "FOUND_LIB-NOTFOUND")
#         find_library(FOUND_LIB NAMES ${libname} HINTS ${mylibdir} NO_DEFAULT_PATH)
#                 IF (FOUND_LIB)
#                         message("found lib: ${FOUND_LIB}")
#                         LIST(APPEND mylibs ${FOUND_LIB})
#                 ELSE()
#                         MESSAGE("not lib found: ${libname}")
#                 ENDIF ()
# endforeach(libname)
#message(${mylibs})

#message(${CPPUNIT_LIBRARY})
