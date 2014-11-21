Sal2
====

To compile with yices 

    cd build
    cmake .. -DYICES_HOME=/home/dejan/Software
    make
    make check

To compile debug mode with yices

    cd build
    cmake .. -DCMAKE_BUILD_TYPE=Debug -DYICES_HOME=/home/dejan/Software 
    make
    make check




