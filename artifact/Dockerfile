FROM letonchanh/dynamite:base

ENV DYNAMITE_HOME=$TOOLSDIR/dynamite
ENV DYNAMITE_DEPS=$TOOLSDIR

COPY ./src $DYNAMITE_HOME/src
COPY ./benchmarks $DYNAMITE_HOME/benchmarks

WORKDIR $DYNAMITE_HOME/benchmarks
