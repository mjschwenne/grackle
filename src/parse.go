package main

import (
	"fmt"
	"log"
	"os"

	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/descriptorpb"
)

var typeMap = map[descriptorpb.FieldDescriptorProto_Type]string{
	descriptorpb.FieldDescriptorProto_TYPE_INT32:   "u32",
	descriptorpb.FieldDescriptorProto_TYPE_UINT32:  "u32",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED32: "u32",
	descriptorpb.FieldDescriptorProto_TYPE_INT64:   "u64",
	descriptorpb.FieldDescriptorProto_TYPE_UINT64:  "u64",
	descriptorpb.FieldDescriptorProto_TYPE_FIXED64: "u64",
	descriptorpb.FieldDescriptorProto_TYPE_MESSAGE: "{{ .GetTypeName }}",
}

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
		messages := fileDescriptorSet.File[0].MessageType
		for _, m := range messages {
			fields := m.GetField()
			// Print some information about the protobuf
			fmt.Printf("---------------------------------------\nMessage: %s\n---------------------------------------\n", m.GetName())
			for i, f := range fields {
				fmt.Printf("Field %v: %s of type %v (%s)\n", i, f.GetName(), f.GetType(), f.GetTypeName())
			}
		}

	} else {
		log.Println("No file descriptors found in the set.")
	}
}
