Dejan: This is a selection of small and solvable btor examples from 
the beem set. Original readme below.

Archive beem-btor version 001 date 2012-04-11

Author:
Jori Dubrovin
Aalto University
Department of Information and Computer Science
jori.dubrovin@aalto.fi


This archive contains the BEEM model checking benchmarks [1]
translated to the sequential BTOR format [2].  The original sources
and authors of the benchmark models are listed in the online BEEM
database [3].

In the subdirectory "btors", each file encodes an instance of a BEEM
model and a reachability property.  The files are named

btors/<model>.<instanceN>.prop<propN>-<circuit>-<trel>.btor

where <model> is the name of the model, <instanceN> is a number
identifying a specific parameterization of the model, and <propN> is a
number identifying a reachability property.  These names and numbers
are as recorded in the BEEM database [3].  All 344 combinations of
instances and reachability properties are included, with various
encoding parameters (see below).  LTL properties are left out, as are
models for which BEEM does not define any reachability properties.

See the file "expected-results.txt" for known model checking results
for most of the instances and reachability properties.  These results
have been computed using an explicit-state model checker.

The translation to BTOR attempts to be bit-accurate and cover all
features of the models.  The control locations are represented with
1-bit registers, the data variables with 8- and 16-bit registers, and
intermediate values with 32-bit signed semantics.  See [4] for more
details.  The encoding parameters <circuit> and <trel> are described
below.  For each instance, two combinations are included.  The
combination func-interl might work better for verifying
non-reachability, while back-serstep might yield witnesses to
reachability faster.

Interleaving transition relation (<trel> = interl):
In each execution step, a single action is executed.  An action
corresponds to a non-synchronizing transition in the BEEM system, or
to a pair of transitions that synchronize on a channel.

Serial exists-step transition relation (<trel> = serstep):
In each execution step of the circuit, one or more actions of the BEEM
system are executed in a sequence.  See [4].

Functional circuit encoding (<circuit> = func):
The register outputs represent the current state xor the initial
state, which is unique in BEEM.  Thus, all-zero register values
represent the initial state.  The register inputs are functionally
dependent on the register outputs and the primary inputs that select
the current actions, according to the transition relation.  The
special register 'dve_invalid' remains 0, unless an action has been
selected whose guard is false.  The reachability property is
conjuncted with 'dve_invalid = 0'.

Backward circuit encoding (<circuit> = back):
A valid execution is such that in the first step, the register inputs
are set to values that satisfy the reachability property, and in all
subsequent steps, the register inputs represent a predecessor state of
the register outputs.  The property to check is whether the register
outputs can represent an initial state after one of more valid
execution steps.  The special register 'dve_initialized' is 1
everywhere except initially, and 'dve_valid' is 1 iff
'dve_initialized' is 1 and the execution is valid so far.


References

[1] R. Pelánek.  BEEM: Benchmarks for Explicit Model Checkers.  In
Proc. SPIN 2007, LNCS vol. 4595, pp. 263--267, Springer 2007.

[2] R. Brummayer, A. Biere, F. Lonsing.  BTOR: Bit-Precise Modelling
of Word-Level Problems for Model Checking.  In Proc. 1st
Intl. Workshop on Bit-Precise Reasoning (BPR'08), Princeton, New
Jersey, USA, July 2008.

[3] http://anna.fi.muni.cz/models/ 14th January 2010.

[4] J. Dubrovin, T. Junttila, K. Heljanko.  Exploiting Step Semantics
for Efficient Bounded Model Checking of Asynchronous Systems.  In
Science of Computer Programming, Elsevier 2011.
http://dx.doi.org/10.1016/j.scico.2011.07.005
