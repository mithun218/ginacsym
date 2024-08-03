# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: CMakeLists.txt                                        #
#                                                             #
# - CMake configuration file to compile ginacsym         #
#                                                             #
# Project name: ginacsym - GiNaC Differential Equation Solver  #
# Contact: Mithun Bairagi <bairagirasulpur@gmail.com>         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 1.7.1                                                #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #


cmake_minimum_required(VERSION 3.6)
project(ginacsym)

INCLUDE(GNUInstallDirs)

# information about the project
set( PROJECT_FULLNAME "ginacsym")
set( PROJECT_DESCRIPTION "ginacSym- a ginac computer algebra system")

# NOTE: On Windows and Cygwin, the dll's are placed in the
# CMAKE_RUNTIME_OUTPUT_DIRECTORY, while their corresponding import
# libraries end up in CMAKE_ARCHIVE_OUTPUT_DIRECTORY. On other
# platforms, such as Linux, the shared libraries are put in
# CMAKE_ARCHIVE_OUTPUT_DIRECTORY instead.
# Static libraries end up in CMAKE_ARCHIVE_OUTPUT_DIRECTORY on all
# platforms.
SET(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/bin)
SET(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/lib)
SET(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/lib)


# The version number.
#set (GINACSYM_VERSION_MAJOR 1)
#set (GINACSYM_VERSION_MINOR 0)
#set(GINACSYM_VERSION_MAINTENANCE 0)

#set( GINACSYM_VERSION "${GINACSYM_VERSION_MAJOR}.${GINACSYM_VERSION_MINOR}.${GINACSYM_VERSION_MAINTENANCE}")
#set( PROJECT_VERSION ${GINACSYM_VERSION} )
#set( GINACSYM_NAME \"${PROJECT_FULLNAME}\")

file(STRINGS ${CMAKE_CURRENT_SOURCE_DIR}/ginacsym/version.h _ginacsym_vinfo REGEX "^#define[\t ]+GINACSYMLIB_.*_VERSION.*")
string(REGEX REPLACE "^.*GINACSYMLIB_MAJOR_VERSION[ \t]+([0-9]+).*" "\\1" GINACSYM_MAJOR_VERSION "${_ginacsym_vinfo}")
string(REGEX REPLACE "^.*GINACSYMLIB_MINOR_VERSION[ \t]+([0-9]+).*" "\\1" GINACSYM_MINOR_VERSION "${_ginacsym_vinfo}")
string(REGEX REPLACE "^.*GINACSYMLIB_MICRO_VERSION[ \t]+([0-9]+).*" "\\1" GINACSYM_MICRO_VERSION "${_ginacsym_vinfo}")

set(GINACSYM_VERSION "${GINACSYM_MAJOR_VERSION}.${GINACSYM_MINOR_VERSION}.${GINACSYM_MICRO_VERSION}")
set( PROJECT_VERSION ${GINACSYM_VERSION} )
set( GINACSYM_NAME \"${PROJECT_FULLNAME}\")


# configure file specification in order to translate CMake variables to C++
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
set( DOLLAR "$" )
#configure_file( ${CMAKE_SOURCE_DIR}/version.h.in ${CMAKE_BINARY_DIR}/versionCMake.h )
configure_file( ${CMAKE_SOURCE_DIR}/ginacsym.pc.cmake.in ${CMAKE_BINARY_DIR}/ginacsym.pc )
include_directories( ${CMAKE_BINARY_DIR} )

# specify pkg-config file to be installed
install( FILES ${CMAKE_BINARY_DIR}/ginacsym.pc DESTINATION lib/pkgconfig )

# add the binary tree to the search path for include files
# so that we will find version.h
include_directories("${PROJECT_BINARY_DIR}")

OPTION(GINACSYM_BUILD_SHARED_LIBS "Build GINACSYM shared library." ON)
OPTION(GINACSYM_BUILD_STATIC_LIBS "Build GINACSYM static library." OFF)
OPTION(GINACSYM_fPIC_BUILD "Build GINACSYM setting POSITION_INDEPENDENT_CODE." ON)

set (CMAKE_CXX_STANDARD 17)

IF(GINACSYM_fPIC_BUILD)
    set(CMAKE_POSITION_INDEPENDENT_CODE ON)
ENDIF()
# path to find own modules
set( CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake )

#for finding external libraries mpfr,gmp,flint, cln, ginac.
find_package (PkgConfig REQUIRED)

pkg_check_modules (GMP REQUIRED gmp>=6.0.0)
include_directories (${GMP_INCLUDE_DIRS})
link_directories (${GMP_LIBRARY_DIRS})

pkg_check_modules (MPFR REQUIRED mpfr>=4.0.0)
include_directories (${MPFR_INCLUDE_DIRS})
link_directories (${MPFR_LIBRARY_DIRS})

pkg_check_modules (FLINT REQUIRED flint>=3.0.0)
include_directories (${FLINT_INCLUDE_DIRS})
link_directories (${FLINT_LIBRARY_DIRS})

pkg_check_modules (CLN REQUIRED cln>=1.3.4)
include_directories (${CLN_INCLUDE_DIRS})
link_directories (${CLN_LIBRARY_DIRS})


set(CORELIBS ${FLINT_LIBRARIES} ${GMP_LIBRARIES} ${MPFR_LIBRARIES} ${CLN_LIBRARIES})

include_directories(${CMAKE_CURRENT_SOURCE_DIR}/ginacsym)
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/ginacsym/parser)
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/ginacsym/polynomial)
link_directories(${GINACSYM_BINARY_DIR}/lib)

SET(GINACSYM_SRCS
    ginacsym/add.cpp
    ginacsym/archive.cpp
    ginacsym/basic.cpp
    ginacsym/clifford.cpp
    ginacsym/color.cpp
    ginacsym/constant.cpp
    ginacsym/ex.cpp
    ginacsym/expair.cpp
    ginacsym/expairseq.cpp
    ginacsym/exprseq.cpp
    ginacsym/factor.cpp
    ginacsym/fail.cpp
    ginacsym/fderivative.cpp
    ginacsym/function.cpp
    ginacsym/functions.cpp
    ginacsym/ginacwrapper.cpp
    ginacsym/idx.cpp
    ginacsym/indexed.cpp
    ginacsym/inert.cpp
    ginacsym/infinity.cpp
    ginacsym/inifcns.cpp
    ginacsym/inifcns_elliptic.cpp
    ginacsym/inifcns_gamma.cpp
    ginacsym/inifcns_hyperb.cpp
    ginacsym/inifcns_integral.cpp
    ginacsym/inifcns_nstdsums.cpp
    ginacsym/inifcns_special.cpp
    ginacsym/inifcns_trans.cpp
    ginacsym/inifcns_trig.cpp
    ginacsym/integral.cpp
    ginacsym/integrate.cpp
    ginacsym/integration_kernel.cpp
    ginacsym/lst.cpp
    ginacsym/map_function.cpp
    ginacsym/matrix.cpp
    ginacsym/mul.cpp
    ginacsym/ncmul.cpp
    ginacsym/normal.cpp
    ginacsym/numeric.cpp
    ginacsym/operators.cpp
    ginacsym/outform.cpp
    ginacsym/parser/default_reader.cpp
    ginacsym/parser/lexer.cpp
    ginacsym/parser/parse_binop_rhs.cpp
    ginacsym/parser/parse_context.cpp
    ginacsym/parser/parser.cpp
    ginacsym/parser/parser_compat.cpp
    ginacsym/polynomial/chinrem_gcd.cpp
    ginacsym/polynomial/collect_vargs.cpp
    ginacsym/polynomial/cra_garner.cpp
    ginacsym/polynomial/divide_in_z_p.cpp
    ginacsym/polynomial/gcd_uvar.cpp
    ginacsym/polynomial/mgcd.cpp
    ginacsym/polynomial/mod_gcd.cpp
    ginacsym/polynomial/normalize.cpp
    ginacsym/polynomial/optimal_vars_finder.cpp
    ginacsym/polynomial/pgcd.cpp
    ginacsym/polynomial/primpart_content.cpp
    ginacsym/polynomial/remainder.cpp
    ginacsym/polynomial/upoly_io.cpp
    ginacsym/power.cpp
    ginacsym/print.cpp
    ginacsym/pseries.cpp
    ginacsym/registrar.cpp
    ginacsym/relational.cpp
    ginacsym/remember.cpp
    ginacsym/simplify.cpp
    ginacsym/solve.cpp
    ginacsym/symbol.cpp
    ginacsym/symmetry.cpp
    ginacsym/tensor.cpp
    ginacsym/utility.cpp
    ginacsym/utils.cpp
    ginacsym/wildcard.cpp
)
SET(GINACSYM_HEADERS
    ginacsym/add.h
    ginacsym/archive.h
    ginacsym/assertion.h
    ginacsym/basic.h
    ginacsym/class_info.h
    ginacsym/clifford.h
    ginacsym/color.h
    ginacsym/compiler.h
    ginacsym/constant.h
    ginacsym/container.h
    ginacsym/crc32.h
    ginacsym/ex.h
    ginacsym/expair.h
    ginacsym/expairseq.h
    ginacsym/exprseq.h
    ginacsym/factor.h
    ginacsym/fail.h
    ginacsym/fderivative.h
    ginacsym/flags.h
    ginacsym/function.h
    ginacsym/functions.h
    ginacsym/ginacsym.h
    ginacsym/ginacsympy.h
    ginacsym/ginacsympy_api.h
    ginacsym/ginacwrapper.h
    ginacsym/hash_map.h
    ginacsym/hash_seed.h
    ginacsym/idx.h
    ginacsym/indexed.h
    ginacsym/inert.h
    ginacsym/infinity.h
    ginacsym/inifcns.h
    ginacsym/integral.h
    ginacsym/integrate.h
    ginacsym/integration_kernel.h
    ginacsym/lst.h
    ginacsym/matrix.h
    ginacsym/mul.h
    ginacsym/ncmul.h
    ginacsym/normal.h
    ginacsym/numeric.h
    ginacsym/operators.h
    ginacsym/outform.h
    ginacsym/parser/debug.h
    ginacsym/parser/lexer.h
    ginacsym/parse_context.h
    ginacsym/parser.h
    ginacsym/polynomial/chinrem_gcd.h
    ginacsym/polynomial/collect_vargs.h
    ginacsym/polynomial/cra_garner.h
    ginacsym/polynomial/debug.h
    ginacsym/polynomial/divide_in_z_p.h
    ginacsym/polynomial/euclid_gcd_wrap.h
    ginacsym/polynomial/eval_point_finder.h
    ginacsym/polynomial/eval_uvar.h
    ginacsym/polynomial/gcd_euclid.h
    ginacsym/polynomial/heur_gcd_uvar.h
    ginacsym/polynomial/interpolate_padic_uvar.h
    ginacsym/polynomial/mod_gcd.h
    ginacsym/polynomial/newton_interpolate.h
    ginacsym/polynomial/normalize.h
    ginacsym/polynomial/optimal_vars_finder.h
    ginacsym/polynomial/pgcd.h
    ginacsym/polynomial/poly_cra.h
    ginacsym/polynomial/prem_uvar.h
    ginacsym/polynomial/primes_factory.h
    ginacsym/polynomial/remainder.h
    ginacsym/polynomial/ring_traits.h
    ginacsym/polynomial/smod_helpers.h
    ginacsym/polynomial/sr_gcd_uvar.h
    ginacsym/polynomial/upoly.h
    ginacsym/polynomial/upoly_io.h
    ginacsym/power.h
    ginacsym/print.h
    ginacsym/pseries.h
    ginacsym/ptr.h
    ginacsym/registrar.h
    ginacsym/relational.h
    ginacsym/remember.h
    ginacsym/simplify.h
    ginacsym/solve.h
    ginacsym/structure.h
    ginacsym/symbol.h
    ginacsym/symmetry.h
    ginacsym/tensor.h
    ginacsym/utility.h
    ginacsym/utils.h
    ginacsym/utils_multi_iterator.h
    ginacsym/version.h
    ginacsym/wildcard.h

)


# Building shared or static library
IF(GINACSYM_BUILD_SHARED_LIBS)
    ADD_LIBRARY(ginacsym SHARED ${GINACSYM_SRCS} ${GINACSYM_HEADERS}
        ginacsym/limit.cpp
        ginacsym/limit.h
        ginacsym/number.cpp
        ginacsym/number.h
        ginacsym/poly_algebra.cpp
        ginacsym/poly_algebra.h
    )
    target_link_libraries(ginacsym PUBLIC ${CORELIBS})
ENDIF()
IF(GINACSYM_BUILD_STATIC_LIBS)
    ADD_LIBRARY(ginacsym_static STATIC ${GINACSYM_SRCS} ${GINACSYM_HEADERS})
    target_link_libraries(ginacsym_static PUBLIC ${CORELIBS})
ENDIF()

add_executable(ginacsym_run ginacsym/main.cpp)
set(ginacsym_runlibs ginacsym ${CORELIBS})
target_link_libraries(ginacsym_run PUBLIC ginacsym ${CORELIBS})

## Testing library
#include(CTest)

#IF(GINACDE_BUILD_SHARED_LIBS)
#    set(testlibs ${CORELIBS} GiNaCDE)
#ENDIF()
#IF(GINACDE_BUILD_STATIC_LIBS)
#    set(testlibs ${CORELIBS} GiNaCDE_static)
#ENDIF()

#add_subdirectory(examples EXCLUDE_FROM_ALL)

#add_executable(test1 test/test1.cpp)
#target_link_libraries(test1 ${testlibs})

#add_executable(test2 test/test2.cpp)
#target_link_libraries(test2 ${testlibs})

#add_executable(checkSolutest1 test/checkSolu_cahnAllen_mF.cpp)
#target_link_libraries(checkSolutest1 ${testlibs})

#add_executable(checkSolutest2 test/checkSolu_Painlev_FIMextravar.cpp)
#target_link_libraries(checkSolutest2 ${testlibs})

#add_test(test1Run ${GINACDE_BINARY_DIR}/bin/test1)
#add_test(test2Run ${GINACDE_BINARY_DIR}/bin/test2)
#add_test(checkSolutest1Run ${GINACDE_BINARY_DIR}/bin/checkSolutest1)
#add_test(checkSolutest2Run ${GINACDE_BINARY_DIR}/bin/checkSolutest2)


# Installing library
IF(GINACSYM_BUILD_SHARED_LIBS)
    install (TARGETS ginacsym
             RUNTIME DESTINATION bin 
             LIBRARY DESTINATION lib
	     ARCHIVE DESTINATION lib)
ENDIF()
IF(GINACSYM_BUILD_STATIC_LIBS)
    install (TARGETS ginacsym_static DESTINATION lib)
ENDIF()

## Installing headers
install(DIRECTORY ginacsym/
        DESTINATION include/ginacsym
        PATTERN "*.cpp" EXCLUDE
        PATTERN "*.in" EXCLUDE
        PATTERN "*.AM" EXCLUDE
        PATTERN "*.in" EXCLUDE) #PATTERN "*/parser" EXCLUDE
#install (FILES ${GINACSYM_HEADERS} DESTINATION include)
#install (FILES "${PROJECT_BINARY_DIR}/versionCMake.h" DESTINATION include/ginacsym)
