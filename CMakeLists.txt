cmake_minimum_required(VERSION 3.16)
project(opmrace)

set(CMAKE_CXX_STANDARD 14)

add_library(opmrace SHARED omprace.cpp)

SET(CMAKE_CXX_FLAGS "-fno-rtti")