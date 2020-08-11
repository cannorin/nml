DOTNET_PATH?=/usr/bin
PREFIX?=/usr/local
REAL_PREFIX=$(shell realpath $(PREFIX))

DOTNET?=$(DOTNET_PATH)/dotnet
GIT?=$(shell which git)
PUBLISH_ARGS=src/interpreter/nml.Interpreter.fsproj -c Release -p:PublishSingleFile=true -p:PublishTrimmed=true -p:PublishReadyToRun=true --self-contained 

all: publish

release:
	$(DOTNET) build -c Release

run: release
	$(DOTNET) run -c Release -p src/interpreter/nml.Interpreter.fsproj

publish-windows:
	$(DOTNET) publish $(PUBLISH_ARGS) --runtime win-x64 -o bin/publish/windows/ 

publish-linux:
	$(DOTNET) publish $(PUBLISH_ARGS) --runtime linux-x64 -o bin/publish/linux/

publish-osx:
	$(DOTNET) publish $(PUBLISH_ARGS) --runtime osx-x64 -o bin/publish/osx/

publish: publish-windows publish-linux publish-osx ;

debug:
	$(DOTNET) build -c Debug

run-debug: debug
	$(DOTNET) run -c Debug -p src/interpreter/nml.Interpreter.fsproj

# Clean

clean:
	$(DOTNET) clean
	$(RM) -r src/core/obj
	$(RM) -r src/interpreter/obj
	$(RM) -r bin/

