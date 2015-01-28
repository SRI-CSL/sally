# Sal2

## Prerequisites

In order to compile SAL you will need the following

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
