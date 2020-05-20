termination-crafted-lit:
#	./run --ejkto=1 --iters=5 termination-crafted-lit list dynamo CookSeeZuleger-TACAS2013-Fig8b.c 
	./run --ejkto=1 --iters=5 termination-crafted-lit list dynamo
	OUTDIR=`cat /tmp/dynamite.outdir`
	./harvest --iters=5 nocsvs termination-crafted-lit/${OUTDIR}
	echo "results are in: termination-crafted-lit/$OUTDIR"
  echo "less compare.tex comparent.tex comparesummary.tex naming.tex"

nla-term:
	./run --ejkto=1 --iters=1 nla-term
	OUTDIR=`cat /tmp/dynamite.outdir`
	echo "results are in: nla-term/$OUTDIR"
	./harvest --iters=1 nocsvs nla-term/${OUTDIR}
# Submission logs: ./harvest nocsvs nla-term/out-7FTS_Zx

nla-nonterm:
	./run --nt=1 --ejkto=1 --iters=1 nla-nonterm
	OUTDIR=`cat /tmp/dynamite.outdir`
	echo "results are in: nla-nonterm/$OUTDIR"
	./harvest --iters=1 nocsvs nla-nonterm/${OUTDIR}
# Submission logs: ./harvest nocsvs nla-nonterm/out-_G_zxz3

integrated:
	./run --integrated=1 --ejkto=1 --iters=1 nla-term dynamo
	OUTDIR=`cat /tmp/dynamite.outdir`
	./harvest nocsvs nla-term/${OUTDIR}
	./run --integrated=1 --ejkto=1 --iters=1 nla-nonterm dynamo
	OUTDIR=`cat /tmp/dynamite.outdir`
	./harvest nocsvs nla-nonterm/${OUTDIR}
# Submission logs:
#./harvest nocsvs nla-nonterm/integrated-hAdQkzM | tail -n 39 > /tmp/all
#./harvest nocsvs nla-term/integrated-XLisaoQ | tail -n 38 >> /tmp/all
