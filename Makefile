all :
	cp src/*.js bin/

deploy :
	cp src/*.js bin/
	cd bin/ ; \
	jison ../src/parser.jison ; \
	cd -

clean :
	rm bin/*
