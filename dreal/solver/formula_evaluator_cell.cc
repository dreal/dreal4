#include "dreal/solver/formula_evaluator_cell.h"

#include <utility>

namespace dreal {

FormulaEvaluatorCell::FormulaEvaluatorCell(Formula f) : f_{std::move(f)} {}

}  // namespace dreal
