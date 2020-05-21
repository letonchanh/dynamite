.PHONY: termination-crafted-lit nla-term nla-nonterm integrated all

## These can be configured
ITERATIONS=1

ALL="termination-crafted-lit nla-term nla-nonterm integrated"

all: ${ALL}

termination-crafted-lit:
	./run --hardtimeout=1 --iters=${ITERATIONS} termination-crafted-lit run dynamo CookSeeZuleger-TACAS2013-Fig8b.c 
#	./run --hardtimeout=1 --iters=${ITERATIONS} termination-crafted-lit list dynamo
	./harvest --iters=${ITERATIONS} nocsvs termination-crafted-lit/`cat /tmp/dynamite.outdir`
	@echo "==> All logs saved to: termination-crafted-lit/`cat /tmp/dynamite.outdir`"
#	@echo "==> TEX Output:  compare.tex comparent.tex comparesummary.tex naming.tex"
	@echo "==> Can re-harvest with:    ./harvest --iters=${ITERATIONS} nocsvs termination-crafted-lit/`cat /tmp/dynamite.outdir`"

nla-term:
	./run --hardtimeout=1 --iters=${ITERATIONS} nla-term run dynamo egcd-both-t.c
	@echo "==> All logs saved to: nla-term/`cat /tmp/dynamite.outdir`"
	./harvest --iters=${ITERATIONS} nocsvs nla-term/`cat /tmp/dynamite.outdir`
	@echo "==> Can re-harvest with:    ./harvest --iters=${ITERATIONS} nocsvs nla-term/`cat /tmp/dynamite.outdir`"
# Submission logs: ./harvest nocsvs nla-term/out-7FTS_Zx

nla-nonterm:
	./run --nt=1 --hardtimeout=1 --iters=${ITERATIONS} nla-nonterm run dynamo fermat1-both-nt.c
	@echo "==> All logs saved to: nla-nonterm/`cat /tmp/dynamite.outdir`"
	./harvest --iters=${ITERATIONS} nocsvs nla-nonterm/`cat /tmp/dynamite.outdir`
	@echo "==> Can re-harvest with:    ./harvest --iters=${ITERATIONS} nocsvs nla-nonterm/`cat /tmp/dynamite.outdir`"
# Submission logs: ./harvest nocsvs nla-nonterm/out-_G_zxz3

integrated:
	./run --integrated=1 --hardtimeout=1 --iters=${ITERATIONS} nla-term  run dynamo egcd-both-t.c
	./harvest nocsvs nla-term/`cat /tmp/dynamite.outdir`
	@echo "==> All logs saved to: nla-term/`cat /tmp/dynamite.outdir`"
	@echo "==> Can re-harvest with:    ./harvest --iters=${ITERATIONS} nocsvs nla-term/`cat /tmp/dynamite.outdir`"
	./run --integrated=1 --hardtimeout=1 --iters=${ITERATIONS} nla-nonterm  run dynamo fermat1-both-nt.c
	./harvest nocsvs nla-nonterm/`cat /tmp/dynamite.outdir`
	@echo "==> All logs saved to: nla-nonterm/`cat /tmp/dynamite.outdir`"
	@echo "==> Can re-harvest with:    ./harvest --iters=${ITERATIONS} nocsvs nla-nonterm/`cat /tmp/dynamite.outdir`"
# Submission logs:
#./harvest nocsvs nla-nonterm/integrated-hAdQkzM | tail -n 39 > /tmp/all
#./harvest nocsvs nla-term/integrated-XLisaoQ | tail -n 38 >> /tmp/all
