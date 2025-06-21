CURRENT_DIR=.
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)

DIRS = \
	lib VC

COQ_FLAG = -R $(SL_DIR)SeparationLogic SimpleC.SL -R $(SL_DIR)unifysl Logic -R $(SL_DIR)Asrtdef SimpleC.ASRT -R $(SL_DIR)AuxiFun SimpleC.ASRTFUN -R $(SL_DIR)Cdef SimpleC.CSE -R $(SL_DIR)sets SetsClass -R $(SL_DIR)compcert_lib compcert.lib -R $(SL_DIR)auxlibs AUXLib -R $(SL_DIR)MonadLib StateMonad -R $(SL_DIR)MonadLib/monadnrm StateMonad.monadnrm -R $(SL_DIR)MonadLib/monaderror StateMonad.monaderror -R $(SL_DIR)fixedpoints FP -R $(SL_DIR)Common SimpleC.Common -R $(SL_DIR)CoreLang SimpleC.CoreLang -R $(SL_DIR)Frontend SimpleC.Frontend -R $(COMMON_STRATEGY_DIR) SimpleC.EE -R . SimpleC.EE

DEP_FLAG = -R $(SL_DIR)SeparationLogic SimpleC.SL -R $(SL_DIR)unifysl Logic -R $(SL_DIR)Asrtdef SimpleC.ASRT -R $(SL_DIR)AuxiFun SimpleC.ASRTFUN -R $(SL_DIR)Cdef SimpleC.CSE -R $(SL_DIR)sets SetsClass -R $(SL_DIR)compcert_lib compcert.lib -R $(SL_DIR)auxlibs AUXLib -R $(SL_DIR)MonadLib StateMonad -R $(SL_DIR)MonadLib/monadnrm StateMonad.monadnrm -R $(SL_DIR)MonadLib/monaderror StateMonad.monaderror -R $(SL_DIR)fixedpoints FP -R $(SL_DIR)Common SimpleC.Common -R $(SL_DIR)CoreLang SimpleC.CoreLang -R $(SL_DIR)Frontend SimpleC.Frontend -R $(COMMON_STRATEGY_DIR) SimpleC.EE -R . SimpleC.EE

lib_FILES = \
	malloc.v sll_tmpl.v ast_lib.v

VC_code_FILE_NAME = thm_apply

strategy_FILE_NAME = 

VC_code_proof_FILES = \
  $(VC_code_FILE_NAME:%=VC/%_goal.v) \
  $(VC_code_FILE_NAME:%=VC/%_proof_auto.v) \
  $(VC_code_FILE_NAME:%=VC/%_proof_manual.v) \
  $(VC_code_FILE_NAME:%=VC/%_goal_check.v) \

strategy_proof_FILES = \
	$(strategy_FILE_NAME:%=VC/%_strategy_goal.v) \
	$(strategy_FILE_NAME:%=VC/%_strategy_proof.v) \
	$(strategy_FILE_NAME:%=VC/%_strategy_goal_check.v) \

FILES = \
  $(lib_FILES:%.v=lib/%.v) \
  $(strategy_proof_FILES:%.v=%.v) \
  $(VC_code_proof_FILES:%.v=%.v) \




$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v


lib : $(lib_FILES:%.v=lib/%.vo)
	@echo Making lib



all : $(FILES:%.v=%.vo)

lib_clean:
	@rm -f lib/*.glob
	@rm -f lib/*.vo
	@rm -f lib/*.vok
	@rm -f lib/*.vos
	@rm -f lib/*.aux

_CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

su:
	docker run --rm -it -u $(id -u):$(id -g) -v /home/venillalemon/FV/prove-2025/qcp-docker/common/:/include/common/ -v /home/venillalemon/FV/prove-2025/qcp/ast/annotated_C/:/include/ast/ -v /home/venillalemon/FV/prove-2025/qcp/ast/VC/:/output/ -v /home/venillalemon/FV/prove-2025/qcp/ast/annotated_C/:/input/ qcp:latest symexec --no-strategy-gen --goal-file=/output/subst_goal.v --proof-auto-file=/output/subst_proof_auto.v --proof-manual-file=/output/subst_proof_manual.v --input-file=/input/subst.c -I/include/common/ -I/include/ast/ -slp /include/ast/ SimpleC.EE

ae:
	docker run --rm -it -u $(id -u):$(id -g) -v /home/venillalemon/FV/prove-2025/qcp-docker/common/:/include/common/ -v /home/venillalemon/FV/prove-2025/qcp/ast/annotated_C/:/include/ast/ -v /home/venillalemon/FV/prove-2025/qcp/ast/VC/:/output/ -v /home/venillalemon/FV/prove-2025/qcp/ast/annotated_C/:/input/ qcp:latest symexec --no-strategy-gen --goal-file=/output/alpha_equiv_goal.v --proof-auto-file=/output/alpha_equiv_proof_auto.v --proof-manual-file=/output/alpha_equiv_proof_manual.v --input-file=/input/alpha_equiv.c -I/include/common/ -I/include/ast/ -slp /include/ast/ SimpleC.EE

ta:
	docker run --rm -it -u $(id -u):$(id -g) -v /home/venillalemon/FV/prove-2025/qcp-docker/common/:/include/common/ -v /home/venillalemon/FV/prove-2025/qcp/ast/annotated_C/:/include/ast/ -v /home/venillalemon/FV/prove-2025/qcp/ast/VC/:/output/ -v /home/venillalemon/FV/prove-2025/qcp/ast/annotated_C/:/input/ qcp:latest symexec --no-strategy-gen --goal-file=/output/thm_apply_goal.v --proof-auto-file=/output/thm_apply_proof_auto.v --proof-manual-file=/output/thm_apply_proof_manual.v --input-file=/input/thm_apply.c -I/include/common/ -I/include/ast/ -slp /include/ast/ SimpleC.EE

clean:
	@rm -f */*.glob
	@rm -f */*.vo	
	@rm -f */*.vok 	
	@rm -f */*.vos	
	@rm -f */.*.aux	
	@rm -f .depend


.PHONY: clean depend
.DEFAULT_GOAL := all

-include .depend

-include $(DEPS)