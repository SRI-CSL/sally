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


# Simple OCaml macros, using ocamlbuild.

find_program(OCAMLBUILD ocamlbuild)
message("-- Found ocamlbuild at ${OCAMLBUILD}")

function (add_ocaml_target RESULT)
	add_custom_target(${RESULT} ALL)
	add_custom_command(TARGET ${RESULT} COMMAND ${OCAMLBUILD} -build-dir "${CMAKE_CURRENT_BINARY_DIR}" ${RESULT} -pkg unix DEPENDS ${ARGN} WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}")
endfunction(add_ocaml_target)
