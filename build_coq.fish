#!/usr/bin/env fish 

set coq_project_args (sed -E -e '/^\#/d' -e "s/'([^']*)'/\1/g" -e 's/-arg //g' -e "/^\s*\$/d" _CoqProject | tr ' ' '\n')
set test_coq_project_args (sed -E -e '/^\#/d' -e "s/'([^']*)'/\1/g" -e 's/-arg //g' -e '/^\s*\$/d' _TestCoqProject | tr ' ' '\n')
fish -c "coqc $coq_project_args $test_coq_project_args $argv[1]"

if test $status = 0
    echo "Complication Successful"
else
    echo "Complication Unsuccessful"
end
