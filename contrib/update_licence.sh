#!/bin/bash

# Goes through the source files, removes the initial comments, and adds the copyright

read -d '' LICENCE << EOF
/**
 * This file is part of sally.
 * Copyright (C) 2015 SRI International.
 *
 * Sally is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Sally is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sally.  If not, see <http://www.gnu.org/licenses/>.
 */
EOF

for file in `find src -name "*.cpp" -or -name "*.h" -or -name "*.g"`;
do 
  echo Processing $file
  (echo "$LICENCE"; perl -0777 -pe 's{^/\*.*?\*/\n*}{\n}s' $file) > tmp; mv tmp $file;
done
