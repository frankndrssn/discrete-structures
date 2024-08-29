.PHONY : all
all :
	@coqdoc -utf8 --parse-comments --no-lib-name *.v

.PHONY : clean
clean :
	@rm -f \
	   *.glob \
	   *.vo \
	   *.vok \
	   *.vos
