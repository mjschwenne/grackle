#!/usr/bin/env fish 

go build $argv
if test $status = 0
    echo "Compliation Successful"
else
    echo "Compliation Unsuccessful"
end
