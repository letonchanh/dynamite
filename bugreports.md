### Bug 1

command:

```
$ python3 dynamo.py ../benchmarks/svcomp-termination-crafted-lit/NoriSharma-FSE2013-Fig8.c -t
```

output:

```
...
analysis:792:DEBUG (_infer_ranking_functions_from_trans) - t2: uk_0 +
327*uk_1 +
298*uk_2 +
-28*uk_3 +
-283*uk_4 +
298*uk_5 +
299*uk_6 +
-283*uk_7
analysis:793:DEBUG (_infer_ranking_functions_from_trans) - rf: -1*y
Traceback (most recent call last):
  File "dynamo.py", line 136, in <module>
    t_prover.prove()
  File "/home/ejk/dynamo/src/analysis.py", line 895, in prove
    rfs = self.infer_ranking_functions(vs, term_itraces)
  File "/home/ejk/dynamo/src/analysis.py", line 749, in infer_ranking_functions
    return self._infer_ranking_functions_from_trans(vs, train_rand_trans)
  File "/home/ejk/dynamo/src/analysis.py", line 815, in _infer_ranking_functions_from_trans
    train_term_rand_trans = list(invalid_train_term_rand_trans)
  File "/home/ejk/dynamo/src/analysis.py", line 802, in <lambda>
    invalid_train_term_rand_trans = itertools.filterfalse(lambda t: (self._check_ranking_function_trans(*t, model)),
  File "/home/ejk/dynamo/src/analysis.py", line 693, in _check_ranking_function_trans
    vt1 = eval(st1)
  File "<string>", line 1
    0 +
      ^
SyntaxError: invalid syntax
```
