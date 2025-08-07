#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include <llvm/IR/Constant.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Dominators.h>
#include <llvm/Analysis/DominanceFrontier.h>
#include <llvm/IR/User.h>
#include <llvm/IR/Value.h>
#include <llvm/Support/Debug.h>
#include <string>
#include <unordered_map>
#include <vector>
#include "ZeroBenefitAnalysis.h"
#include "developing.h"
#include "utils.h"
#include "GraphBuilder.h"
#include "userop.h"
class BlocksCloneHelper
{
    using BasicBlock = llvm::BasicBlock;
    using Instruction = llvm::Instruction;
    // block map from origin to clones
    std::unordered_map<BasicBlock *, BasicBlock *> block_map;
    // new blocks
    std::vector<BasicBlock *> new_blocks;
    // instr map from origin to clones
    std::unordered_map<Instruction *, llvm::UserOp2Inst *> _instr_map;
    // succ blocks may need to handle phinode
    std::set<BasicBlock *> org_succ_blocks;

    llvm::Instruction *instr_map(Instruction *instr)
    {
        auto iter = _instr_map.find(instr);
        if (iter != _instr_map.end())
        {
            return llvm::cast<Instruction>(iter->second->getOperand(0));
        }
        return nullptr;
    }

private:
    bool is_cloned_block(BasicBlock *block)
    {
        return block->getName().ends_with(".clone") && block->getName().starts_with(opt_zone_prefix);
    }
    bool is_optzone_block(BasicBlock *block) { return block_map.find(block) != block_map.end(); }

private:
    bool reachable_to_dsts(const ValueGraph &block_graph, BasicBlock *src, const std::set<BasicBlock *> &dsts)
    {
        bool reachable = false;
        for (auto dst : dsts)
        {
            if (block_graph.reachable(src, dst))
            {
                reachable = true;
                break;
            }
        }
        return reachable;
    }
    std::string opt_zone_prefix;

public:
    ~BlocksCloneHelper()
    {
        for (auto [_, inst] : _instr_map)
        {
            auto userop2 = llvm::cast<llvm::UserOp2Inst>(inst);
            // userop2->setOperand(0, nullptr);
            llvm::UserOp2Inst::Destory(userop2);
        }
    }
    BasicBlock *operator[](BasicBlock *block) { return block_map[block]; }

    llvm::Value *operator[](Instruction *instr) { return _instr_map[instr]->getOperand(0); }

    bool contains(Instruction *instr) { return _instr_map.find(instr) != _instr_map.end(); }

    BlocksCloneHelper(llvm::BasicBlock *zero_header,
                      const std::vector<BasicBlock *> &blocks,
                      llvm::Value *v,
                      ValueGraph &block_graph,
                      llvm::DominatorTree &dt,
                      llvm::DominanceFrontier &df,
                      const std::string &opt_zone_prefix)
    : opt_zone_prefix(opt_zone_prefix)
    {
        using namespace llvm;

        my_dbg() << *blocks[0]->getParent() << "\n";

        int block_id = 0;
        for (auto *block : blocks)
        {
            // if (block->getName() == "")
            // {
            //     block->setName("opt_zone" + std::to_string(block_id++));
            // }
            BasicBlock *new_block =
                BasicBlock::Create(block->getContext(), block->getName() + ".clone", block->getParent());
            block_map[block] = new_block;
            new_blocks.push_back(new_block);
        }
        my_dbg() << *v << "\n";
        my_dbg() << "v type: " << *v->getType() << "\n";
        llvm::Value *zero =nullptr; 
        if (v->getType()->isVectorTy())
        {
            zero = llvm::Constant::getNullValue(v->getType());
        }
        else
        {
            zero = v->getType()->isIntegerTy() ? llvm::ConstantInt::get(v->getType(), 0)
                                                            : llvm::ConstantFP::get(v->getType(), 0);
        }
        std::unordered_map<Instruction *, std::unordered_map<llvm::BasicBlock *, llvm::Instruction *>> instr_defs;
        // succ -> {prev}, prev branch to succ
        std::unordered_map<llvm::BasicBlock *, std::vector<llvm::BasicBlock *>> succ_prev_blocks;
        for (auto *block : blocks)
        {
            auto new_block = block_map[block];
            for (auto &instr : *block)
            {
                auto *new_instr = instr.clone();
                _instr_map[&instr] = UserOp2Inst::Create(new_instr, UserOp2Inst::Type::CloneHelper);
                for (auto op = new_instr->op_begin(), op_end = new_instr->op_end(); op != op_end; ++op)
                {
                    if (op->get() == v)
                    {
                        op->set(zero);
                    }
                }
                new_instr->insertInto(new_block, new_block->end());
            }
        }
        for (auto *block : blocks)
        {
            for (auto &instr : *block)
            {
                auto *new_instr = instr_map(&instr);
                // for switch case, a switch inst can have multiple edges to the same block
                // we need to update phinode in the block only once
                std::set<llvm::BasicBlock *> processed_blocks;
                // instr_defs[&instr][instr.getParent()] = &instr;

                // update every op of cloned instr
                for (auto [i, op] : enumerate(new_instr->operands()))
                {
                    // update op for cloned instr: a = func(b) -> a' = func(b')
                    if (auto *op_instr = dyn_cast<Instruction>(op))
                    {
                        auto val = instr_map(op_instr);
                        if (val != nullptr)
                        {
                            new_instr->setOperand(i, val);
                        }
                    }
                    // update phi for cloned instr: a = phi(b) -> a' = phi(b')
                    if (auto phi = dyn_cast<PHINode>(new_instr))
                    {
                        auto *op_block = phi->getIncomingBlock(i);
                        auto iter = block_map.find(op_block);
                        if (iter != block_map.end())
                        {
                            phi->setIncomingBlock(i, iter->second);
                        }
                    }
                    // update branch for cloned instr: branch a -> b -> a' -> b'
                    if (auto *op_block = dyn_cast<BasicBlock>(op))
                    {
                        auto iter = block_map.find(op_block);
                        // for switch case, a switch inst can have multiple edges to the same block
                        // so we need to update every edge, therefore "processed_blocks" is in the else block
                        if (iter != block_map.end())
                        {
                            // block branch a->b -- a'->b'
                            new_instr->setOperand(i, iter->second);
                        }
                        else
                        {
                            if (instr.isDebugOrPseudoInst())
                            {
                                continue;
                            }
                            if (processed_blocks.find(op_block) != processed_blocks.end())
                            {
                                continue;
                            }
                            // update phi in succ
                            org_succ_blocks.insert(op_block);
                            my_dbg() << "update phi for " << *op_block << "\n";
                            succ_prev_blocks[op_block].push_back(block);
                            for (auto &phi : op_block->phis())
                            {
                                // different inst can have the same op block, so we need to update phi only once
                                // for example, if there are two phinode using different values in succ block,
                                // when we update the first phi,
                                // the second phi may be updated automatically, so we don't need to update it again
                                std::vector<std::pair<Value *, llvm::BasicBlock *>> updates;
                                for (auto [j, op] : enumerate(phi.operands()))
                                {
                                    // As we will update phi for every incoming block,
                                    // every incoming block only update their own incoming value
                                    if (phi.getIncomingBlock(j) == block)
                                    {
                                        // If is instruction ,we need to judge whether it is cloned
                                        if (isa<Instruction>(phi.getIncomingValue(j)))
                                        {
                                            auto *phi_op = cast<Instruction>(phi.getIncomingValue(j));
                                            auto iter = _instr_map.find(phi_op);
                                            if (iter == _instr_map.end())
                                            {
                                                // phi.addIncoming(phi_op, block_map[block]);
                                                updates.push_back({phi_op, block_map[block]});
                                            }
                                            else
                                            {
                                                // phi.addIncoming(instr_map(phi_op), block_map[block]);
                                                updates.push_back({instr_map(phi_op), block_map[block]});
                                            }
                                        }
                                        else
                                        {
                                            // phi.addIncoming(phi.getIncomingValue(j), block_map[block]);
                                            updates.push_back({phi.getIncomingValue(j), block_map[block]});
                                        }
                                        break;
                                    }
                                }
                                for (auto [v, b] : updates)
                                {
                                    my_dbg() << "update phi for succ: " << phi << "block: " << b->getName() << "\n";
                                    phi.addIncoming(v, b);
                                }
                            }
                        }
                    }
                }
            }
        }

        std::unordered_set<llvm::BasicBlock *> processed;
        // update phi for use pos which is outside of the cloned blocks
        for (auto *block : blocks)
        {
            for (auto &inst : *block)
            {
                std::set<BasicBlock *> use_pos_set;
                // search where the instruction is used
                // if the user is in the cloned blocks, we don't need to update phi
                // if the user is phi-node in the succ blocks, we don't need to update phi
                for (auto user : inst.users())
                {
                    if (isa<UserOp2Inst>(user))
                    {
                        continue;
                    }
                    if (auto user_inst = dyn_cast<Instruction>(user))
                    {
                        // for debug, program should never enter this branch
                        if (is_cloned_block(user_inst->getParent()))
                        {
                            my_dbg() << "inst whose user in cloned block: " << inst << "\n";
                            my_dbg() << "user in cloned block: " << *user_inst << "\n";
                        }
                        if (is_optzone_block(user_inst->getParent()))
                        {
                            continue;
                        }
                        // If user is a phinode, we don't consider the parent block as the use position.
                        // Instead, we consider the incoming block as the use position.
                        // Also, we don't need to update phi for the cloned block or blocks in optzone
                        if (auto phi = dyn_cast<PHINode>(user))
                        {
                            for (auto [i, op] : enumerate(phi->operands()))
                            {
                                if (op.get() == &inst && !is_optzone_block(phi->getIncomingBlock(i)) &&
                                    !is_cloned_block(phi->getIncomingBlock(i)))
                                {
                                    use_pos_set.insert(phi->getIncomingBlock(i));
                                }
                            }
                        }
                        else
                        {
                            use_pos_set.insert(user_inst->getParent());
                        }
                    }
                }

                auto org_use_pos_set = use_pos_set;

                std::vector<llvm::BasicBlock *> defs;
                std::set<llvm::BasicBlock *> new_defs;
                std::set<llvm::Instruction *> new_created_phis;

                // for succ block A and B, we need to insert phi for both A and B.
                // if A can reach to B, and we process B before A, there will be no incoming value from A to B
                // so we need to delay the incoming value insertion
                std::vector<std::pair<BasicBlock *, PHINode *>> delayed_phis;
                // insert phi for each instr in the succ blocks
                // initialize defs with succ which can reach to the use pos
                for (auto succ : org_succ_blocks)
                {
                    for (auto use_pos : use_pos_set)
                    {
                        my_dbg() << "reachable: " << block_graph.reachable(succ, use_pos) << "\n";
                        my_dbg() << "succ: " << *succ << "\n";
                        my_dbg() << "use pos: " << *use_pos << "\n";
                        // for A --> zero_header --> A, we don't need to insert phi for A
                        if (block_graph.reachable(succ, use_pos) && !dt.dominates(succ, zero_header))
                        {
                            defs.push_back(succ);
                            auto phi = PHINode::Create(inst.getType(),
                                                       2 * succ_prev_blocks[succ].size(),
                                                       inst.getName() + ".phi",
                                                       &succ->front());
                            new_created_phis.insert(phi);
                            // for each incoming block, insert incoming value
                            // if a block is a user of the inst, then the parent block is the incoming block
                            // now we consider the user can branch, invoke or switch
                            // basicblock is not the op of phi-node.
                            for (auto user : succ->users())
                            {
                                if (isa<UserOp2Inst>(user))
                                {
                                    continue;
                                }
                                if (auto user_inst = dyn_cast<Instruction>(user))
                                {
                                    if (isa<BranchInst, InvokeInst, SwitchInst>(user_inst))
                                    {
                                        auto prev_block = user_inst->getParent();
                                        if (is_optzone_block(prev_block))
                                        {
                                            phi->addIncoming(&inst, prev_block);
                                            phi->addIncoming(instr_map(&inst), block_map[prev_block]);
                                        }
                                        else if (is_cloned_block(prev_block))
                                        {
                                            continue;
                                        }
                                        // If the user is not in optzone or cloned block,
                                        // the incoming value may not be ready.
                                        // so we need to delay the incoming value insertion
                                        else
                                        {
                                            // phi->addIncoming(phi, prev_block);
                                            delayed_phis.push_back({prev_block, phi});
                                            my_dbg() << "delayed phi for " << *prev_block << ": " << *phi << "\n";
                                        }
                                    }
                                }
                            }
                            my_dbg() << "phi: " << *phi << "\n";
                            instr_defs[&inst][succ] = phi;
                            break;
                        }
                    }
                }
                // my_dbg() << "---------------------------------------------\n";
                // my_dbg() << "start updating dominator frontier\n";
                while (true)
                {
                    // Try to update value in use pos with defs.
                    // If the def block dominates the use pos, we can update the value.
                    // After updating, we can remove the use pos from the set.
                    for (auto def_iter = defs.begin(); def_iter != defs.end();)
                    {
                        bool def_is_valid = false;
                        auto def = *def_iter;
                        for (auto use_pos_iter = use_pos_set.begin(); use_pos_iter != use_pos_set.end();)
                        {
                            auto use_pos = *use_pos_iter;
                            // my_dbg() << "update source inst: " << inst << "\n";
                            // my_dbg() << "update inst for use pos: " << *use_pos << "\n";
                            if (dt.dominates(&def->front(), use_pos) || def->front().getParent() == use_pos)
                            {
                                use_pos_iter = use_pos_set.erase(use_pos_iter);
                                // update non-phi-node user
                                inst.replaceUsesWithIf(instr_defs[&inst].at(def), [use_pos](auto &use) {
                                    return isa<Instruction>(use.getUser()) &&
                                           cast<Instruction>(use.getUser())->getParent() == use_pos &&
                                           !isa<PHINode, UserOp2Inst>(use.getUser());
                                    //    new_created_phis.find(cast<Instruction>(use.getUser())) ==
                                    //        new_created_phis.end();
                                });
                                // update phi-user in the succ blocks
                                inst.replaceUsesWithIf(instr_defs[&inst].at(def), [use_pos, this, v](auto &use) {
                                    return (isa<Instruction>(use.getUser()) && isa<PHINode>(use.getUser()) &&
                                            dyn_cast<PHINode>(use.getUser())->getIncomingBlock(use) == use_pos &&
                                            !is_optzone_block(use_pos) && !is_cloned_block(use_pos)) ||
                                           (isa<UserOp2Inst>(use.getUser()) &&
                                            cast<UserOp2Inst>(use.getUser())->_t != UserOp2Inst::Type::CloneHelper &&
                                            cast<UserOp2Inst>(use.getUser())->zero_instr != v);
                                    //    new_created_phis.find(cast<Instruction>(use.getUser())) ==
                                    //        new_created_phis.end();
                                });
                            }
                            else
                            {
                                def_is_valid = true;
                                ++use_pos_iter;
                            }
                        }
                        // If def block doesn't dominate any use pos, we can remove it from defs.
                        if (!def_is_valid)
                        {
                            def_iter = defs.erase(def_iter);
                        }
                        else
                        {
                            ++def_iter;
                        }
                    }
                    if (defs.empty())
                    {
                        break;
                    }
                    // Insert phi-nodes in the dominance frontier of the defs.
                    // Replace the defs with the frontiers.
                    for (auto def : defs)
                    {
                        my_dbg() << "def: " << *def << "\n";
                        auto frontiers_iter = df.find(def);
                        if (frontiers_iter == df.end())
                        {
                            my_dbg() << "no frontier for " << *def << "\n";
                            throw nullptr;
                        }
                        auto &frontiers = df.find(def)->second;
                        auto def_inst = instr_defs[&inst].at(def);
                        for (auto frontier : frontiers)
                        {
                            my_dbg() << "frontier: " << *frontier << "\n";

                            // If the frontier is not reachable to the use pos, we don't need to insert phi.
                            if (!reachable_to_dsts(block_graph, frontier, org_use_pos_set))
                            {
                                my_dbg() << "skip frontier: " << *frontier << "\n";
                                continue;
                            }

                            // A frontier may be dominance frontier of multiple def blocks.
                            // We only need to insert phi once.
                            auto [iter, no_phi] = instr_defs[&inst].try_emplace(frontier);
                            if (no_phi)
                            {
                                auto phi = PHINode::Create(
                                    inst.getType(), 0, inst.getName() + ".indirect.phi", &frontier->front());
                                iter->second = phi;
                                new_created_phis.insert(phi);
                            }
                            auto phi = cast<PHINode>(iter->second);
                            // update phi in the frontier block for every incoming block
                            for (auto frontier_user : frontier->users())
                            {
                                if (auto incoming_block_branch_to_frontier = dyn_cast<Instruction>(frontier_user))
                                {
                                    if (isa<BranchInst, InvokeInst, SwitchInst>(incoming_block_branch_to_frontier))
                                    {
                                        auto prev_block = incoming_block_branch_to_frontier->getParent();
                                        int count = 0;
                                        if (auto switch_inst = dyn_cast<SwitchInst>(incoming_block_branch_to_frontier))
                                        {
                                            for (auto _i = 0; _i < switch_inst->getNumSuccessors(); ++_i)
                                            {
                                                auto succ = switch_inst->getSuccessor(_i);
                                                if (succ == frontier)
                                                {
                                                    count++;
                                                }
                                            }
                                        }
                                        else
                                        {
                                            count = 1;
                                        }
                                        int already_have_count = 0;
                                        for (auto [i, op] : enumerate(phi->operands()))
                                        {
                                            if (phi->getIncomingBlock(i) == prev_block)
                                            {
                                                already_have_count++;
                                            }
                                        }
                                        if ((dt.dominates(def_inst, prev_block) || def_inst->getParent() == prev_block))
                                        {
                                            my_dbg() << "add incoming for " << *phi << " from " << *def_inst << "\n";
                                            for (int i = 0; i < count - already_have_count; ++i)
                                            {
                                                phi->addIncoming(def_inst, prev_block);
                                            }
                                        }
                                        else if (dt.dominates(frontier, prev_block))
                                        {
                                            for (int i = 0; i < count - already_have_count; ++i)
                                            {
                                                phi->addIncoming(phi, prev_block);
                                            }
                                        }
                                        else
                                        {
                                            delayed_phis.push_back({prev_block, phi});
                                        }
                                    }
                                }
                            }
                            new_defs.insert(frontier);
                            // if the phi is complete, we can update the use pos with def in the frontier block
                            if (phi->isComplete())
                            {
                                for (auto use_pos_iter = use_pos_set.begin(); use_pos_iter != use_pos_set.end();)
                                {
                                    auto use_pos = *use_pos_iter;
                                    // my_dbg() << "frontier: " << *frontier << "\n";
                                    // my_dbg() << "use pos: " << *use_pos << "\n";
                                    if (dt.dominates(frontier, use_pos))
                                    {
                                        use_pos_iter = use_pos_set.erase(use_pos_iter);
                                        inst.replaceUsesWithIf(phi, [use_pos](auto &use) {
                                            return isa<Instruction>(use.getUser()) &&
                                                   cast<Instruction>(use.getUser())->getParent() == use_pos &&
                                                   !isa<PHINode, UserOp2Inst>(use.getUser());
                                        });
                                        inst.replaceUsesWithIf(
                                            instr_defs[&inst].at(frontier), [use_pos, this, v](auto &use) {
                                                return (isa<Instruction>(use.getUser()) &&
                                                        isa<PHINode>(use.getUser()) &&
                                                        dyn_cast<PHINode>(use.getUser())->getIncomingBlock(use) ==
                                                            use_pos &&
                                                        !is_optzone_block(use_pos) && !is_cloned_block(use_pos)) ||
                                                       (isa<UserOp2Inst>(use.getUser()) &&
                                                        cast<UserOp2Inst>(use.getUser())->_t !=
                                                            UserOp2Inst::Type::CloneHelper &&
                                                        cast<UserOp2Inst>(use.getUser())->zero_instr != v);
                                                //    new_created_phis.find(cast<Instruction>(use.getUser())) ==
                                                //        new_created_phis.end();
                                            });
                                    }
                                    else
                                    {
                                        ++use_pos_iter;
                                    }
                                }
                            }
                        }
                    }
                    defs.clear();
                    for (auto def : new_defs)
                    {
                        defs.push_back(def);
                    }
                    new_defs.clear();
                }

                // for (auto [_, phis] : delayed_phis)
                {
                    // my_dbg() << "delayed phis for " << *def << "\n";
                    for (auto [block, phi] : delayed_phis)
                    {
                        my_dbg() << "use block: " << *block << "\n";
                        my_dbg() << "use block for phi: " << *phi << "\n";
                        for (auto def : instr_defs[&inst])
                        {
                            my_dbg() << "def block: " << *def.first << "\n";
                            my_dbg() << "nearest common dominator: " << *dt.findNearestCommonDominator(def.first, block)
                                     << "\n";
                            if (auto *def_inst = dyn_cast<Instruction>(def.second))
                            {
                                my_dbg() << "def inst: " << *def_inst << "\n";
                                if (dt.dominates(def.first, block) || def_inst->getParent() == block)
                                {
                                    my_dbg() << "dominates!!\n";
                                    if (phi->getBasicBlockIndex(block) == -1)
                                    {
                                        phi->addIncoming(def_inst, block);
                                    }
                                    break;
                                }
                            }
                        }
                        // if (instr_defs[&inst].find(def) == instr_defs[&inst].end())
                        // {
                        //     my_dbg() << "no phi for " << *phi << "inst " << inst << " defined " << *def
                        //            << "\nwhose prev is" << *block << "\n";
                        // }
                        // // phi->setIncomingValueForBlock(block, instr_defs[&inst].at(def));
                        // phi->addIncoming(instr_defs[&inst].at(def), block);
                    }
                }
            }
        }
    }
};