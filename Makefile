ignores = --ignore=deesi/theories/RCF/test_simplify_motor_redlog.txt

.PHONY: pytest pytest-full test-doc mypy test test-all doc pygount\
		coverage coverage_html clean veryclean conda-build

pytest:
	pytest -n 8 --doctest-cython --exitfirst --doctest-modules $(ignores)

pytest-fast:
	PYTHONOPTIMIZE=TRUE pytest -n 8 --disable-warnings --exitfirst --doctest-modules $(ignores)

pytest-seq:
	pytest --doctest-cython --exitfirst --doctest-modules $(ignores)

pytest-full:
	pytest -n 8 --doctest-modules $(ignores)

pytest-full-seq:
	pytest --doctest-modules $(ignores)

test-doc:
	cd doc && make test

mypy:
	mypy --explicit-package-bases stubs
	mypy deesi

test: mypy pytest

test-all: test test-doc

doc:
	cd doc && make clean html

pygount:
	pygount -f summary deesi

coverage:
	coverage run -m pytest --doctest-modules

coverage_html: coverage
	coverage html
	open htmlcov/index.html

veryclean:
	rm -rf htmlcov .coverage
