.PHONY: compile run clean
.DEFAULT_GOAL := compile

compile:
	agda -i src --compile src/Main.agda

run: compile
	./src/Main

clean:
	rm -f src/Main
	rm -rf src/MAlonzo/
	find . -name "*.agdai" -delete
