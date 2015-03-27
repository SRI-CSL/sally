# Sally

## Prerequisites

In order to compile Sally you will need the following

* A reasonable c++ compiler such as g++ or clang
    ```
    sudo apt-get install g++
    ```
* The CMake build system 
    ```
    sudo apt-get install cmake
    ```

* The GMP library
    ```
    sudo apt-get install libgmp-dev
    ```
* Some Boost libraries
    ```
    sudo apt-get install libboost-program-options-dev libboost-iostreams-dev libboost-test-dev
    ```
* A working Java runtime 
    ```
    sudo apt-get install default-jre
    ```

## How to Compile

If you've installed Yices2 in the $YD directory, meaning that there are 
$YD/include and $YD/lib directories with Yices2 headers and libraries, then
build with 

    cd build
    cmake .. -DYICES2_HOME=$YD
    make
    make check

If you've installed MathSAT in the $MD directory, meaning that there are 
$MD/include and $MD/lib directories with MathSAT5 headers and libraries, then 
build with

    cd build
    cmake .. -DMATHSAT5_HOME=$MD
    make
    make check
   
You can use both Yices2 and MathSAT by adding both options to cmake as expected.

To compile in debug mode then pass on

    cd build
    cmake .. -DCMAKE_BUILD_TYPE=Debug
    make
    make check

### Input Language

#### Transition System Definition 

Sally takes as input a simple description of transition systems based on the 
SMT2 language. A transition system consists of a description of the state type, 
a formula describing the initial states of the system, and a formula describing 
the transitions from the current to the next state of the system.

State type is just a list of variables that are pare of the state, together with
their types.

    ;; A definition of a state type called "my_state_type" with variables
    ;; x and y of type Real. 
    (define-state-type my_state_type 
      ((x Real) (y Real))
    )

With a defined state type, we can define sets of states and transition over the
state type and sate transitions over the state type.

We can describe a set of states with a state formula over the state type. A 
state formula is a first-order formula over the variables of the state type, 
written in SMT2 format.

    ;; Definition of a set of states "x_is_zero" capturing all states 
    ;; over the state type "my_state_type" where x is 0.
    (define-states x_is_zero my_state_type
      (= x 0)
    )

Once a state formula has been defined it can be reused in other state formulas
over the same state type.

    ;; A definition of a set of states "initial_states" over 
    ;; "my_state_type" by a state formula. These are all states where 
    ;; both x and y are 0.
    (define-states initial_states my_state_type
      (and x_is_zero (= y 0))
    )
    
We can describe allowed state transitions by a first-order formula over the 
current (state) and next variables of the state type. We use the prefix
``state`` to denote current variables and the prefix ``next`` to denote the 
variables in the next state. Previously defined state formulas over the same
state type can be used as if they were variables (state or next). Similarly, 
previously defined transitions over the same type can be used directly. 

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

We can define a state transition system by defining the state type, the initial
states of the system and the transitions that the system can make.

    ;; Directly define a simple counter system that increases x and y
    (define-transition-system T1 my_state_type
       ;; Initial states 
       (and (= x 0) (= y 0))
       ;; Transition 
       (and (= next.x (+ state.x 1)) (= next.y (+ state.y 1)))
    )
    
    ;; Define a counter system that can reset to 0 by reusing defined
    ;; formulas 
    (define-transition-system T2 my_state_type
       ;; Initial states
       initial_states
       ;; Transitions 
       transition
    )
    
#### Queries

A query asks a question whether a state property is true in the given transition 
system. For example, in the system ``T1``, it is clear that we have that the 
variables ``x`` and ``y`` will always be equal and non-negative. We can check 
these with the following queries.

    ;; Check whether x = y in T1
    (query T1 (= x y))

    ;; Check whether x, y >= 0
    (query T1 (and (>= x 0) (>= y 0)))
    
In the system ``T2``, it should hold that both ``x`` and ``y`` will never 
exceed 20. 

    ;; Check whether x, y <= 20
    (query T2 (and (<= x 20) (<= y 20)))
    
    ;; Check whether x, y <= 19
    (query T2 (and (<= x 19) (<= y 19)))
    
The example above is available in ``examples/example.mcmt``.
    
### Usage 

To see the full set of options run ``sally -h``. Some typical examples are as 
follows

* Checking the properties with the bounded model-checking (bmc) engine
    ```
    sally --engine bmc examples/example.mcmt
    unknown
    unknown
    unknown
    unknown
    ```
* Checking the property with BMC with a bigger bound and showin any 
counter-example traces
    ```
    sally --engine bmc --bmc-max 20 --show-trace examples/example.mcmt
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
    ```  
* Checking the properties with the k-induction (kind) engine
    ```
    sally --engine kind examples/example.mcmt
    valid
    valid
    unknown
    unknown 
    sally --engine kind --kind-max 20 examples/example.mcmt 
    valid
    valid
    unknown
    invalid
    ```
* Checking the properties with the ic3 engine using the combination of yices2
  and MathSAT5 as the reasoning engine
    ```
    sally --engine ic3 --solver y2m5 examples/example.mcmt 
    valid
    valid
    valid
    invalid
    ```
