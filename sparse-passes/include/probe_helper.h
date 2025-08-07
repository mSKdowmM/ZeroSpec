#pragma once
#include "probe.h"
#include "llvm/IR/Instructions.h"
#include <vector>
bool is_instrument_check(const llvm::Value *call);
bool is_instrument(const llvm::Value *call);
void search_instrumetation_calls(llvm::Function &F, std::vector<llvm::CallInst *> &instrument_checks);
void search_instrumetation_check_calls(llvm::Function &F, std::vector<llvm::CallInst *> &instrument_checks);
llvm::CallInst *search_allocate_buffer_call(llvm::Function &F);
int get_instrumeitation_id_in_func(llvm::CallInst *call);
llvm::Value *get_instrumentation_target(llvm::Value *call);
void remove_instrumentations(llvm::Function &F);
