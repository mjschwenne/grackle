//go:build !goose

package main

import (
	"fmt"
)

func main() {
	// This simple example creates a new event, then marshals and unmarshals it into
	// a new Event before printing the result.

	event := Event{name: "Grackle Meeting", start: TimeStamp{hour: 13, minute: 00, second: 00}, end: TimeStamp{hour: 14, minute: 00, second: 00}}
	fmt.Printf("Name:  %v\nStart: %02d:%02d:%02d\nEnd:   %02d:%02d:%02d\n", event.name, event.start.hour, event.start.minute, event.start.second, event.end.hour, event.end.minute, event.end.second)

	enc := MarshalEvent(&event)

	var newEvent *Event
	newEvent = UnmarshalEvent(enc)

	fmt.Printf("Name:  %v\nStart: %02d:%02d:%02d\nEnd:   %02d:%02d:%02d\n", newEvent.name, newEvent.start.hour, newEvent.start.minute, newEvent.start.second, newEvent.end.hour, newEvent.end.minute, newEvent.end.second)
}
