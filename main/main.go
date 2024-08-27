package main

import (
	"fmt"
	"time"
)

func main() {
	// This simple example creates a new time stamp, then marshals and unmarshals it into
	// a new TimeStamp before printing the result.

	hours, minutes, seconds := time.Now().Clock()
	fmt.Printf("True Time:   %v:%v:%v\n", hours, minutes, seconds)
	timeStamp := TimeStamp{hour: uint32(hours), minute: uint32(minutes), second: uint32(seconds)}
	enc := timeStamp.marshal()

	var newTime *TimeStamp
	var err error
	newTime, err = UnmarshalTimeStamp(enc)
	if err != nil {
		fmt.Println(err.Error())
	}

	fmt.Printf("Struct Time: %v:%v:%v\n", newTime.hour, newTime.minute, newTime.second)
}
