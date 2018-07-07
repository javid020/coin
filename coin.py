from constraint import Problem, ExactSumConstraint
import sys


def solve():
    problem = Problem()
    total = 3.00
    variables = ("0.02", "0.09", "0.13", "1.50", "2.00")
    values = [float(x) for x in variables]
    for variable, value in zip(variables, values):
        problem.addVariable(variable, range(int(total / value)))
    problem.addConstraint(ExactSumConstraint(total, values), variables)
    problem.addConstraint(ExactSumConstraint(100))
    solutions = problem.getSolutionIter()
    return solutions, variables


def main():
    solutions, variables = solve()
    for i, solution in enumerate(solutions):
        sys.stdout.write("%d -> " % (i + 1))
        for variable in variables:
            sys.stdout.write("%s coins %d times, " % (variable, solution[variable]))
        sys.stdout.write("\n")


if __name__ == "__main__":
    main()
