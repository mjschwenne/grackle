package main

import (
	"fmt"
	"log"
	"os"

	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/descriptorpb"
)

func main() {
	descriptorFile := "src/timestamp_type.bin"
	descriptorContent, err := os.ReadFile(descriptorFile)
	if err != nil {
		log.Fatalf("Failed to read descriptor file: %v", err)
	}

	// Check if the file is not empty
	if len(descriptorContent) == 0 {
		log.Fatalf("Descriptor file is empty")
	}

	// Unmarshal the descriptor into a FileDescriptorSet
	var fileDescriptorSet descriptorpb.FileDescriptorSet
	if err := proto.Unmarshal(descriptorContent, &fileDescriptorSet); err != nil {
		log.Fatalf("Failed to unmarshal descriptor file: %v", err)
	}

	// Access the first FileDescriptorProto
	if len(fileDescriptorSet.File) > 0 {
		fields := fileDescriptorSet.File[0].MessageType[0].GetField()

		// Print some information about the protobuf
		for i, f := range fields {
			fmt.Printf("Field %v: %s of type %v\n", i, *f.Name, f.Type)
		}
	} else {
		log.Println("No file descriptors found in the set.")
	}
}
