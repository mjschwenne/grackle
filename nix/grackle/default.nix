{
  buildGoModule,
  protobuf,
  ...
}:
buildGoModule {
  pname = "grackle";
  version = "new";
  src = ../../.;
  vendorHash = "sha256-j/lpVHa9v0rLoUyU8uFkO7Uz8gPMOPPTZQXiLeyooyk=";
  nativeBuildInputs = [protobuf];
}
