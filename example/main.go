//go:build !goose

package main

import (
	"fmt"
)

func main() {
	// This simple example creates a new event, then marshals and unmarshals it into
	// a new Event before printing the result.

	event := Event{id: 1, name: "test event", startTime: TimeStamp{hour: 13, minute: 00, second: 00}, endTime: TimeStamp{hour: 14, minute: 00, second: 00}}
	fmt.Printf("Name:  %s\nStart: %02d:%02d:%02d\nEnd:   %02d:%02d:%02d\n", event.name, event.startTime.hour, event.startTime.minute, event.startTime.second, event.endTime.hour, event.endTime.minute, event.endTime.second)

	enc := MarshalEvent(event, []byte{})

	var newEvent Event
	newEvent, _ = UnmarshalEvent(enc)

	fmt.Printf("Name:  %s\nStart: %02d:%02d:%02d\nEnd:   %02d:%02d:%02d\n", newEvent.name, newEvent.startTime.hour, newEvent.startTime.minute, newEvent.startTime.second, newEvent.endTime.hour, newEvent.endTime.minute, newEvent.endTime.second)
}
