# This file is part of sally.
# Copyright (C) 2015 SRI International.
#
# Sally is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# Sally is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with sally.  If not, see <http://www.gnu.org/licenses/>.


# Find opam
find_program(OPAM_BIN opam PATHS ${OPAM})

# If opam found check for components
if (OPAM_BIN)

  # Get the opam version
  execute_process(COMMAND ${OPAM_BIN} --version OUTPUT_VARIABLE OPAM_VERSION OUTPUT_STRIP_TRAILING_WHITESPACE ERROR_QUIET)
  message(STATUS "Opam version: ${OPAM_VERSION}")

  # Get the ocaml version
  execute_process(COMMAND ${OPAM_BIN} config exec -- ocaml -version OUTPUT_VARIABLE VERSION_TEST_RUN_OUTPUT ERROR_QUIET)
  if("${VERSION_TEST_RUN_OUTPUT}" MATCHES "The OCaml toplevel, version ([0-9]*\\.[0-9]*\\.[0-9]*)")
    set(OCAML_VERSION "${CMAKE_MATCH_1}")
  else()
    set(OCAML_VERSION "unknown")
  endif()
  message(STATUS "OCaml version: ${OCAML_VERSION}")

  # Check the components
  foreach(COMPONENT ${Opam_FIND_COMPONENTS})
    # Run the check
    execute_process(
      COMMAND
        ${OPAM_BIN} show -f version ${COMPONENT}
      RESULT_VARIABLE COMPONENT_EXITCODE
      OUTPUT_VARIABLE COMPONENT_VERSION OUTPUT_STRIP_TRAILING_WHITESPACE
      ERROR_QUIET
    )

    # Found if exitcode = 0
    if(NOT ${COMPONENT_EXITCODE})
      message (STATUS "  ${COMPONENT} version ${COMPONENT_VERSION}")
    else()
      message (STATUS "  ${COMPONENT} NOT FOUND")
      set(OPAM_MISSING_PACKAGE 1)
    endif()
  endforeach()

endif()

if (NOT OPAM_BIN)
  message(FATAL_ERROR "Could not find Opam")
endif()

if (OPAM_MISSING_PACKAGE)
  message(FATAL_ERROR "Opam packages missing")
endif()

# Generic OCAML target to be build with opam and ocamlbuild
function (add_ocaml_target RESULT)
  add_custom_target(${RESULT} ALL)
  add_custom_command(TARGET ${RESULT}
    COMMAND
      ${OPAM_BIN} config exec --
        ocamlbuild
          -use-ocamlfind
          -build-dir "${CMAKE_CURRENT_BINARY_DIR}" ${RESULT}
          -pkg unix
    DEPENDS ${ARGN}
    WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
  )
endfunction(add_ocaml_target)
