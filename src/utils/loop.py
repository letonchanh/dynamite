class LoopPart(object):
    def __init__(self, inp_decls, cond, transrel):
        self.inp_decls = inp_decls
        self.cond = cond
        self.transrel = transrel

class Stem(LoopPart):
    pass

class Loop(LoopPart):
    pass

class LoopInfo(object):
    def __init__(self, stem, loop):
        self.stem = stem
        self.loop = loop