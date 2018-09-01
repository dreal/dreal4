#pragma once

#include <memory>
#include <unordered_map>
#include <vector>

#include "./ibex.h"

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {
/// Visitor class which converts a symbolic Formula into
/// ibex::ExprCtr.
class IbexConverter {
 public:
  /// Delete the default constructor.
  IbexConverter() = delete;

  /// Constructs a converter from @p variables.
  explicit IbexConverter(const std::vector<Variable>& variables);

  /// Constructs a converter from @p box.
  explicit IbexConverter(const Box& box);

  ///@{ Delete copy/move constructors and copy/move assign operations.
  IbexConverter(const IbexConverter&) = delete;
  IbexConverter& operator=(const IbexConverter&) = delete;
  IbexConverter(IbexConverter&&) = delete;
  IbexConverter& operator=(IbexConverter&&) = delete;
  ///@}

  /// Destructor. If `need_to_delete_variables_` is set, delete
  /// `ibex::ExprSymbol*` in `symbolic_var_to_ibex_var_`.
  ~IbexConverter();

  /// Convert @p f into the corresponding IBEX data structure,
  /// ibex::ExprCtr*.
  ///
  /// @note It is caller's responsibility to delete the return value.
  /// @note So far, it is always the case that the returned value is
  /// used to construct an `ibex::Function` object. Simply deleting
  /// `ibex::ExprCtr` does not destruct the included `ibex::ExprNode`
  /// objects. However, `ibex::Function`'s destructor does the job. As
  /// a result, we should not call `ibex::cleanup` function explicitly
  /// with the return value of this method.
  const ibex::ExprCtr* Convert(const Formula& f);

  const ibex::Array<const ibex::ExprSymbol>& variables() const;

  void set_need_to_delete_variables(bool value);

 private:
  // Convert @p e into the corresponding IBEX data structure,
  // ibex::ExprNode*.
  //
  // @note See the above note in `Convert(const Formula& f)`.
  const ibex::ExprNode* Convert(const Expression& e);

  // Visits @p e and converts it into ibex::ExprNode.
  const ibex::ExprNode* Visit(const Expression& e);
  const ibex::ExprNode* VisitVariable(const Expression& e);
  const ibex::ExprNode* VisitConstant(const Expression& e);
  const ibex::ExprNode* VisitRealConstant(const Expression& e);
  const ibex::ExprNode* VisitAddition(const Expression& e);
  const ibex::ExprNode* VisitMultiplication(const Expression& e);
  const ibex::ExprNode* VisitDivision(const Expression& e);
  const ibex::ExprNode* VisitLog(const Expression& e);
  const ibex::ExprNode* VisitAbs(const Expression& e);
  const ibex::ExprNode* VisitExp(const Expression& e);
  const ibex::ExprNode* VisitSqrt(const Expression& e);
  const ibex::ExprNode* ProcessPow(const Expression& base,
                                   const Expression& exponent);
  const ibex::ExprNode* VisitPow(const Expression& e);
  const ibex::ExprNode* VisitSin(const Expression& e);
  const ibex::ExprNode* VisitCos(const Expression& e);
  const ibex::ExprNode* VisitTan(const Expression& e);
  const ibex::ExprNode* VisitAsin(const Expression& e);
  const ibex::ExprNode* VisitAcos(const Expression& e);
  const ibex::ExprNode* VisitAtan(const Expression& e);
  const ibex::ExprNode* VisitAtan2(const Expression& e);
  const ibex::ExprNode* VisitSinh(const Expression& e);
  const ibex::ExprNode* VisitCosh(const Expression& e);
  const ibex::ExprNode* VisitTanh(const Expression& e);
  const ibex::ExprNode* VisitMin(const Expression& e);
  const ibex::ExprNode* VisitMax(const Expression& e);
  const ibex::ExprNode* VisitIfThenElse(const Expression&);
  const ibex::ExprNode* VisitUninterpretedFunction(const Expression&);

  // Visits @p e and converts it into ibex::ibex::ExprNode.
  const ibex::ExprCtr* Visit(const Formula& f, bool polarity);
  const ibex::ExprCtr* VisitFalse(const Formula&, bool);
  const ibex::ExprCtr* VisitTrue(const Formula&, bool);
  const ibex::ExprCtr* VisitVariable(const Formula&, bool);
  const ibex::ExprCtr* VisitEqualTo(const Formula& f, bool polarity);
  const ibex::ExprCtr* VisitNotEqualTo(const Formula& f, bool polarity);
  const ibex::ExprCtr* VisitGreaterThan(const Formula& f, bool polarity);
  const ibex::ExprCtr* VisitGreaterThanOrEqualTo(const Formula& f,
                                                 bool polarity);
  const ibex::ExprCtr* VisitLessThan(const Formula& f, bool polarity);
  const ibex::ExprCtr* VisitLessThanOrEqualTo(const Formula& f, bool polarity);
  const ibex::ExprCtr* VisitConjunction(const Formula&, bool);
  const ibex::ExprCtr* VisitDisjunction(const Formula&, bool);
  const ibex::ExprCtr* VisitNegation(const Formula& f, bool polarity);
  const ibex::ExprCtr* VisitForall(const Formula&, bool);

  // ---------------
  // Member fields
  // ---------------
  // Set of domain variables.
  const std::vector<Variable>& vars_;

  // True if we need to delete the variables (ibex::ExprSymbol
  // objects) in the destructor. At initialization, this is true. But
  // when `Convert()` method returns a non-null pointer, it changes to
  // false assuming that the caller will delete the variables.
  bool need_to_delete_variables_{true};

  // Variable → ibex::ExprSymbol*.
  std::unordered_map<Variable, const ibex::ExprSymbol*, hash_value<Variable>>
      symbolic_var_to_ibex_var_;

  ibex::Array<const ibex::ExprSymbol> var_array_;

  // Represents the value `0.0`. We use this to avoid possible
  // memory-leak caused by IBEX code: See
  // https://github.com/ibex-team/ibex-lib/blob/af48e38847414818913b6954e1b1b3050aa14593/src/symbolic/ibex_ExprCtr.h#L53-L55
  const ibex::ExprNode* zero_;

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend const ibex::ExprCtr*
  drake::symbolic::VisitFormula<const ibex::ExprCtr*>(IbexConverter*,
                                                      const Formula&,
                                                      const bool&);
  // Makes VisitExpression a friend of this class so that it can use private
  // operator()s.
  friend const ibex::ExprNode*
  drake::symbolic::VisitExpression<const ibex::ExprNode*>(IbexConverter*,
                                                          const Expression&);
};

}  // namespace dreal
