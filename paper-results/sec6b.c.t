__main__:102:INFO (<module>) - Dynamite's logger_level: DEBUG
__main__:103:INFO (<module>) - Dig's logger_level: WARNING
__main__:104:INFO (<module>) - Timeout: 300s
__main__:106:INFO (<module>) - 2020-05-15 13:27:01.843661: dynamo.py ../benchmarks/paper/sec6b.c -t
/home/exp/tools/SageMath/local/lib/python3.7/site-packages/pyximport/pyximport.py:51: DeprecationWarning: the imp module is deprecated in favour of importlib; see the module's documentation for alternative uses
  import imp
analysis:72:DEBUG (__init__) - Create C source for mainQ: /var/tmp/Dig_o0_pu5c_
analysis:80:DEBUG (__init__) - trans_cmd: /home/exp/eric/dynamo/deps/dynamo-instr/src/cil/bin/cilly --save-temps -D HAPPY_MOOD --dotransform /home/exp/eric/dynamo/benchmarks/paper/sec6b.c --out=/var/tmp/Dig_o0_pu5c_/sec6b.c --bnd=500
analysis:87:DEBUG (__init__) - cg: defaultdict(<class 'list'>, {'vloop_11': ['exit'], 'mainQ': ['vloop_11'], 'main': ['mainQ']})
analysis:98:DEBUG (__init__) - postorder_vloop_ids: ['vloop_11']
analysis:107:DEBUG (__init__) - inp_decls (<class 'data.prog.Symbs'>): I x
analysis:108:DEBUG (__init__) - inv_decls (<class 'data.prog.DSymbs'>): {'vtrace1_11': (Symb(name='x', typ='I'),), 'vtrace2_11': (Symb(name='x', typ='I'),), 'vtrace3_11': (Symb(name='x', typ='I'),)}
__main__:152:DEBUG (<module>) - prove_process: 21962
lib:43:DEBUG (gen_rand_inps) - gen 100/100 random inps
utils.profiling:31:DEBUG (timed) - gen_rand_inps: 47.66ms
lib:54:DEBUG (get_traces_from_inps) - inp_decls: I x
lib:55:DEBUG (get_traces_from_inps) - inv_decls: {'vtrace1_11': (Symb(name='x', typ='I'),), 'vtrace2_11': (Symb(name='x', typ='I'),), 'vtrace3_11': (Symb(name='x', typ='I'),)}
utils.profiling:31:DEBUG (timed) - _get_traces_mp: 157.02ms
utils.profiling:31:DEBUG (timed) - _merge_traces: 317.96ms
utils.profiling:31:DEBUG (timed) - get_traces_from_inps: 475.53ms
analysis:1101:DEBUG (prove) - itraces: 100
analysis:1107:DEBUG (prove) - Analysing Termination vloop_11
analysis:1046:DEBUG (prove_term_vloop) - classify_inps: vloop_11
analysis:1049:DEBUG (prove_term_vloop) - itraces: 100
lib:208:DEBUG (print_inps) - x=-28: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-290: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=272: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-30: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=271: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-23: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=18: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=292: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=21: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-288: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=14: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-8: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=6: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-9: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=287: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=19: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-17: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=297: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-5: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=291: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=296: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-18: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=279: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=7: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-282: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=286: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=273: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-289: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=11: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-277: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=4: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-299: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-285: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-19: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=26: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-281: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-300: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=295: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-15: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-10: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-286: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=28: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-294: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=22: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-292: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=277: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-27: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-22: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-280: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=16: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=276: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=15: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=285: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=27: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-20: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-291: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-11: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-2: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=1: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=23: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-287: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=10: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-1: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=274: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-3: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-14: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=5: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=289: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=12: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-29: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-275: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-26: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-284: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-273: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=13: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-271: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=9: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-279: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-274: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-13: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=278: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-21: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=270: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=17: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=8: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-24: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=0: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-12: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=284: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-278: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=283: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=25: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-7: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-283: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=29: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-4: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=298: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-25: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=-6: [('vtrace1_11', 1), ('vtrace2_11', 500)]
lib:208:DEBUG (print_inps) - x=3: [('vtrace1_11', 1), ('vtrace2_11', 500)]
analysis:1051:DEBUG (prove_term_vloop) - base_term_inps: 0
analysis:1052:DEBUG (prove_term_vloop) - term_inps: 0
analysis:1053:DEBUG (prove_term_vloop) - mayloop_inps: 100
analysis:863:DEBUG (infer_ranking_functions) - vloop: vloop_11
analysis:864:DEBUG (infer_ranking_functions) - term_itraces: 0
utils.profiling:31:DEBUG (timed) - infer_ranking_functions: 0.05ms
analysis:1067:DEBUG (prove_term_vloop) - validate_ranking_functions: vloop_11
analysis:994:DEBUG (validate_ranking_functions) - ranks_str: 
validate:123:DEBUG (gen_validate_file) - validate_cmd: /home/exp/eric/dynamo/deps/dynamo-instr/src/cil/bin/cilly --save-temps -D HAPPY_MOOD --dovalidate /home/exp/eric/dynamo/benchmarks/paper/sec6b.c --out=/var/tmp/Dig_o0_pu5c_/vloop_11/par/validate/sec6b.c --pos=11 --ranks=""
validate:41:DEBUG (prove_reach) - pcmd: /home/exp/tools/CPAchecker-1.9-unix/scripts/cpa.sh -spec /home/exp/tools/reachability.prp -predicateAnalysis -setprop counterexample.export.compressWitness=false /var/tmp/Dig_o0_pu5c_/vloop_11/par/validate/sec6b.c
validate:41:DEBUG (prove_reach) - pcmd: /home/exp/tools/ultimate/releaseScripts/default/UAutomizer-linux/Ultimate.py --spec /home/exp/tools/reachability.prp --architecture 32bit --witness-dir /var/tmp/Dig_o0_pu5c_/vloop_11/par/uatm --witness-name witness.graphml --file /var/tmp/Dig_o0_pu5c_/vloop_11/par/validate/sec6b.c
validate:41:DEBUG (prove_reach) - pcmd: /home/exp/tools/ultimate/releaseScripts/default/UTaipan-linux/Ultimate.py --spec /home/exp/tools/reachability.prp --architecture 32bit --witness-dir /var/tmp/Dig_o0_pu5c_/vloop_11/par/utp --witness-name witness.graphml --file /var/tmp/Dig_o0_pu5c_/vloop_11/par/validate/sec6b.c
validate:46:DEBUG (prove_reach) - res: False
validate:61:DEBUG (validate_witness) - vcmd: /home/exp/tools/CPAchecker-1.9-unix/scripts/cpa.sh -spec /home/exp/tools/reachability.prp -witnessValidation -witness /var/tmp/Dig_o0_pu5c_/vloop_11/par/cpa/output/Counterexample.1.graphml /var/tmp/Dig_o0_pu5c_/vloop_11/par/validate/sec6b.c
validate:46:DEBUG (prove_reach) - res: False
validate:61:DEBUG (validate_witness) - vcmd: /home/exp/tools/ultimate/releaseScripts/default/UAutomizer-linux/Ultimate.py --spec /home/exp/tools/reachability.prp --architecture 32bit --validate /var/tmp/Dig_o0_pu5c_/vloop_11/par/uatm/witness.graphml --file /var/tmp/Dig_o0_pu5c_/vloop_11/par/validate/sec6b.c
validate:46:DEBUG (prove_reach) - res: False
validate:61:DEBUG (validate_witness) - vcmd: /home/exp/tools/ultimate/releaseScripts/default/UTaipan-linux/Ultimate.py --spec /home/exp/tools/reachability.prp --architecture 32bit --validate /var/tmp/Dig_o0_pu5c_/vloop_11/par/utp/witness.graphml --file /var/tmp/Dig_o0_pu5c_/vloop_11/par/validate/sec6b.c
validate:49:DEBUG (prove_reach) - validate_witness: DONE
validate:50:DEBUG (prove_reach) - cex: None
validate:253:DEBUG (prove_reach) - wrs: [('cpa', (False, None))]
validate:256:DEBUG (prove_reach) - Got result firstly from cpa
utils.profiling:31:DEBUG (timed) - prove_reach: 3731.92ms
analysis:1007:DEBUG (validate_ranking_functions) - r: False
utils.profiling:31:DEBUG (timed) - validate_ranking_functions: 3867.77ms
analysis:1069:DEBUG (prove_term_vloop) - Termination result (vloop_11): False ([])
utils.profiling:31:DEBUG (timed) - prove_term_vloop: 3871.58ms
utils.profiling:31:DEBUG (timed) - prove: 4405.99ms
utils.profiling:31:DEBUG (timed) - prove: 4406.39ms
Termination result: None
Time log:
gen_rand_inps: 0.048s
_get_traces_mp: 0.157s
_merge_traces: 0.318s
get_traces_from_inps: 0.476s
infer_ranking_functions: 0.000s
prove_reach: 3.732s
validate_ranking_functions: 3.868s
prove_term_vloop: 3.872s
prove: 4.406s
