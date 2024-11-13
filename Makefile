# Some bits about go.
GOPATH := $(shell go env GOPATH)
GOBIN := $(if $(shell go env GOBIN),$(shell go env GOBIN),$(GOPATH)/bin)

# Defines the linter version.
LINT_VERSION=v1.61.0

.PHOMY: lint
lint:
	@go install github.com/golangci/golangci-lint/cmd/golangci-lint@$(LINT_VERSION)
	$(GOBIN)/golangci-lint run --timeout=10m ./...

.PHONY: test
test: 
	go test -v ./...
