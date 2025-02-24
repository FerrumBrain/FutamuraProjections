cmake_minimum_required(VERSION 3.30)
project(FlowchartFutamura)

set(CMAKE_CXX_STANDARD 20)

add_executable(FlowchartFutamura main.cpp
        FlowchartProgramState.h
        FlowchartInterpreter.h
        Util.h
        Statement.h
        FlowchartBlock.h
        FlowchartList.h
        TuringMachineProgram.h
        FlowchartProgram.h
        Value.h
        AdditionalUtil.h
        Forward.h)
