[![Build Status](https://travis-ci.org/SRI-CSL/sally.svg?branch=master)](https://travis-ci.org/SRI-CSL/sally)
[![Coverage Status](https://coveralls.io/repos/SRI-CSL/sally/badge.svg?branch=master)](https://coveralls.io/r/SRI-CSL/sally?branch=master)
[![Coverity Scan Build Status](https://scan.coverity.com/projects/5578/badge.svg)](https://scan.coverity.com/projects/5578)

# Sally

Sally is a model checker for infinite state systems described as transition 
systems. It is research software under development so the features and the 
input language may change rapidly.   

The project is supported by NASA contract NNX14AI05A.

## Prerequisites

In order to compile Sally you will need a reasonable c++ compiler such as g++ or clang, the cmake build system, the GMP library, some boost libraries, and a working Java runtime (for parser generation). On Ubuntu-like systems, the following should cover it:
```bash
sudo apt-get install g++
sudo apt-get install cmake
sudo apt-get install libgmp-dev
sudo apt-get install libboost-program-options-dev libboost-iostreams-dev libboost-test-dev libboost-thread-dev libboost-system-dev
sudo apt-get install default-jre
```
In addition, Sally needs an SMT solver for reasoning about the systems. It currently supports [Yices2](http://yices.csl.sri.com/) and [MathSAT5](http://mathsat.fbk.eu/). For best results we recommend using both Yices2 and MathSAT5. 

## How to Compile

If you have Yices2 installed in the $YD directory, meaning that there are 
$YD/include and $YD/lib directories with Yices2 headers and libraries, then
configure and build with 
```bash
cd build
cmake .. -DYICES2_HOME=$YD
make
make check
```
If you have MathSAT5 installed in the $MD directory, meaning that there are 
$MD/include and $MD/lib directories with MathSAT5 headers and libraries, then 
configure and build with
```bash
cd build
cmake .. -DMATHSAT5_HOME=$MD
make
make check
```

To compile sally in debug mode then configure and build with
```bash
cd build
cmake .. -DCMAKE_BUILD_TYPE=Debug
make
make check
```

In order to use the non-linear capabilities of Yices2 in Sally, the 
version of Yices2 used mused be compiled with MCSAT enabled, and LibPoly 
must be available. Similar to above, you can pass `-DLIBPOLY_HOME=$LPD` 
to cmake if LibPoly is installed in a non-standard location. 

### Input Language

Sally takes as input a simple description of transition systems based on the 
SMT2 language. A transition system consists of a description of the state type, 
a formula describing the initial states of the system, and a formula describing 
the transitions from the current to the next state of the system.

#### State Types

State type is a list of variables that are part of the state, together with
their types.
```lisp
;; A definition of a state type called "my_state_type" with variables
;; x and y of type Real. 
(define-state-type my_state_type 
  ((x Real) (y Real))
)
```
Sometimes it is useful to model systems that take inputs that are not part of the system state. Such inputs can be defined by using the more general form of state type definition.
```lisp
;; State type with inputs 
(define-state-type state_type_with_inputs
  ((x Real) (y Real))
  ((d Real)) 
)
```
Above, the variable ``d`` is such an input. These input variables can only be referenced in transition formulas, by using the ``input`` namespace.

With a defined state type, we can define sets of states and transitions over the
state type.

#### State Formulas

We can describe a set of states with a state formula over the state type. A 
state formula is a first-order formula over the variables of the state type, 
written in SMT2 format.
```lisp
;; Definition of a set of states "x_is_zero" capturing all states 
;; over the state type "my_state_type" where x is 0.
(define-states x_is_zero my_state_type
  (= x 0)
)
```
Once a state formula has been defined it can be reused in other state formulas
over the same state type.
```lisp
;; A definition of a set of states "initial_states" over 
;; "my_state_type" by a state formula. These are all states where 
;; both x and y are 0.
(define-states initial_states my_state_type
  (and x_is_zero (= y 0))
)
```   

#### State Transitions

We can describe allowed state transitions by a first-order formula over the 
current (state) and next variables of the state type. We use the prefix
``state`` to denote current variables, and the prefix ``next`` to denote the 
variables in the next state. Previously defined state formulas over the same
state type can be used as if they were variables (state or next). Similarly, 
previously defined transitions over the same type can be used directly. 
```lisp
;; Definition of a transition where the next value of x is the 
;; current value + 1.
(define-transition inc_x my_state_type
  (= next.x (+ state.x 1))
)   
    
;; Definition of a transition that increases both x and y
(define-transition inc_x_and_y my_state_type
  (and inc_x (= next.y (+ state.y 1)))
)
    
;; Definition of a transition that increases x and y if not 
;; exceeding 100, or goes back to the state with x = y = 0
(define-transition transition my_state_type
  (or 
    (and (< state.x 100) inc_x_and_y)
    next.initial_states
  ) 
)
```

#### Transition Systems

We can define a state transition system by defining the state type, the initial
states of the system and the transitions that the system can make.
```lisp
;; Directly define a simple counter system that increases x and y
(define-transition-system T1 my_state_type
  ;; Initial states 
  (and (= x 0) (= y 0))
  ;; Transition 
  (and (= next.x (+ state.x 1)) (= next.y (+ state.y 1)))
)
    
;; Define the counter system that can reset to 0 by reusing defined
;; formulas 
(define-transition-system T2 my_state_type
   ;; Initial states
   initial_states
   ;; Transitions 
   transition
)

;; Transition system with inputs 
(define-transition-system T3 state_type_with_inputs
  (and (= x 0) (= y 0))
  (and (= next.x (+ state.x input.d))
   (= next.y (+ state.y input.d))
  )
)
```

#### Queries

A query asks whether a state property is invariant for the given transition 
system (i.e., whether the state property is true in all reachable states). 
For example, in the system ``T1``, it is clear that we the 
variables ``x`` and ``y`` will always be equal and non-negative. We can check 
these with the following queries.
```lisp
;; Check whether x = y in T1
(query T1 (= x y))

;; Check whether x, y >= 0
(query T1 (and (>= x 0) (>= y 0)))
```

In the system ``T2``, it should hold that both ``x`` and ``y`` will never 
exceed 20. 
```lisp
;; Check whether x, y <= 20
(query T2 (and (<= x 20) (<= y 20)))
    
;; Check whether x, y <= 19
(query T2 (and (<= x 19) (<= y 19)))
```

In the system ``T3``, the variables ``x`` and ``y`` should always be equal.
```lisp
;; Check whether we're always the same 
(query T3 (= x y))
```

The full example above is available in ``examples/example.mcmt``.
    
### Usage 

To see the full set of options, run ``sally -h``. Some typical examples are as 
follows

* Checking the properties with the bounded model-checking (BMC) engine
```bash
> sally --engine bmc examples/example.mcmt
unknown
unknown
unknown
unknown
unknown
```
    
* Checking the property with BMC with a bigger bound and showing any 
counter-example traces
```bash
> sally --engine bmc --bmc-max 20 --show-trace examples/example.mcmt
unknown
unknown
unknown
invalid
(trace 
  (frame (x 0) (y 0))
  (frame (x 1) (y 1))
  ...
  (frame (x 20) (y 20))
)
unknown
```
    
* Checking the properties with the k-induction engine
```bash
> sally --engine kind examples/example.mcmt
valid
valid
unknown
unknown
valid
> sally --engine kind --kind-max 20 examples/example.mcmt 
valid
valid
unknown
invalid
valid
```
    
* Checking the properties with the pdkind engine using the combination of yices2
  and MathSAT5 as the reasoning engine
```bash
> sally --engine pdkind --solver y2m5 examples/example.mcmt 
valid
valid
valid
invalid
valid
```

* Checking nonlinear properties with Yices2 

By relying on Yices2 with support for MCSAT, you can use Sally to reason 
about (polynomial) non-linear systems using BMC and k-induction. The
following example models two systems computing sums `S1 = 1 + 2 + ... + n` and
`S2 = 1^2 + 2^2 + ... + n^2`, and asks whether `S1 = n*(n+1)/2` and 
`S2 = n*(n+1)*(2n+1)/6`. 

```lisp
;; Maintain Sum and n
(define-state-type ST ((Sum Real) (n Real)))
;; Initial states: Sum = 0, n = 0
(define-states Init ST (and (= Sum 0) (= n 0)))

;; Transition: Sum += n; n ++;
(define-transition Trans1 ST (and 
  (= next.Sum (+ state.Sum state.n))
  (= next.n (+ state.n 1))
))   

;; Transition system: Sum = 1 + 2 + ... + (n-1)
(define-transition-system T1 ST Init Trans1)
;; Sum = n*(n-1)/2
(query T1 (= Sum (/ (* n (- n 1)) 2)))

;; Transition: Sum += n^2; n ++;
(define-transition Trans2 ST (and 
    (= next.Sum (+ state.Sum (* state.n state.n)))
    (= next.n (+ state.n 1))
))   

;; Transition system: Sum = 1^2 + 2^2 + ... + (n-1)^2
(define-transition-system T2 ST Init Trans2)
;; Sum = n*(n-1)/2
(query T2 (= Sum (/ (* n (- n 1) (- (* 2 n) 1)) 6)))

```

We can prove these two properties with Sally by using Yices2 with MCSAT 
as follows

```bash
> sally --engine kind ../examples/example-nra.mcmt
valid
valid
```


  

