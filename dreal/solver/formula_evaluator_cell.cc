#include "dreal/solver/formula_evaluator_cell.h"

#include <utility>

namespace dreal {

using std::move;

FormulaEvaluatorCell::FormulaEvaluatorCell(Formula f) : f_{move(f)} {}

}  // namespace dreal
