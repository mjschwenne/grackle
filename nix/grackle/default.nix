{
  buildGoModule,
  protobuf,
  ...
}:
buildGoModule {
  pname = "grackle";
  version = "new";
  src = ../../.;
  vendorHash = "sha256-tx+UiQWfXq9AJ/JQdGy9qw7VTKKVQ8D1CFAyN/wNU8w=";
  nativeBuildInputs = [protobuf];
}
