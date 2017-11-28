sample.pdf: oolong.ott.tex sample.tex
	pdflatex sample.tex

oolong.ott.tex: oolong.ott
	ott -merge false -show_defns true -sort true -show_sort true oolong.ott -o oolong.ott.tex -tex_wrap false

clean:
	rm -f oolong.ott.tex
	rm -f *.log *.aux *.log