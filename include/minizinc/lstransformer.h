/* -*- mode: C++; c-basic-offset: 2; indent-tabs-mode: nil -*- */

/*
 *  Main authors:
 *      Gustav Bjordal <gustav.bjordal@it.uu.se>
 */

/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef LIBMINIZINC_LSTRANSFORMER_H
#define LIBMINIZINC_LSTRANSFORMER_H


#include <iostream>
#include <string>
#include <minizinc/model.hh>
#include <minizinc/astiterator.hh>
#include <minizinc/model.hh>
#include <minizinc/astexception.hh>
#include <minizinc/copy.hh>
#include "ast.hh"

namespace MiniZinc {

  namespace LSConstants {
    static constexpr const char *AND = "neighborhood_and";
    static constexpr const char *POSTCOND = "ensuring";
    static constexpr const char *PRECOND = "where";
    static constexpr const char *MOVES = "moves";
    static constexpr const char *INITIALLY = "initially";
    static constexpr const char *DEFINES_GENERATOR = "defines_generator";
    static constexpr const char *NEIGHBORHOOD_DEFINITION = "neighborhood_definition";
    static constexpr const char *VOID = "void";
    static constexpr const char *NEIGHBORHOOD_DECL = "neighborhood_declaration";
    static constexpr const char *ASSIGN_OP = "':='";
    static constexpr const char *SWAP_OP = "':=:'";
    static constexpr const char *ASSIGN = "assign";
    static constexpr const char *SWAP = "swap";
    static constexpr const char *ASSIGN_ARRAY = "assign_array";
    static constexpr const char *SWAP_ARRAY = "swap_array";
  };

  namespace LSTransformation {
    static Call *createFlatFunctionAndCall(EnvI &env, Type &returnType,
                                           const Location &loc,
                                           std::string name,
                                           std::vector<VarDecl *> funcParam,
                                           Expression *body,
                                           std::vector<Expression *> &callArgs) {
      FunctionI *function = env.create_function(returnType, name, funcParam, body);
      function->ann().add(constants().ann.flat_function);
      return new Call(loc, function->id().str(), callArgs, function);
    }
    
    static Call *createFlatFunctionAndCall(EnvI &env, Type &returnType,
                                           const Location &loc,
                                           std::string name,
                                           std::vector<VarDecl *> funcParam,
                                           std::vector<Expression *> &body,
                                           Expression *returnE,
                                           std::vector<Expression *> &callArgs) {

      Let *functionBody = new Let(loc, body, returnE);
      return createFlatFunctionAndCall(env, returnType, loc, name, funcParam, functionBody, callArgs);
    }
  };

  class CallFinder : public EVisitor {
  private:
    std::string _callName;
    std::vector<Call *> _foundCalls;
  protected:

  public:
    CallFinder() : _callName("") {}

    CallFinder(std::string callName) : _callName(callName) {}

    /// Visit call
    void vCall(Call &c) {
      if (c.id().str() == _callName) {
        _foundCalls.push_back(&c);
      }
    }

    const std::vector<Call *> &getFoundCalls() const {
      return _foundCalls;
    }

    /// Determine whether to enter node
    bool enter(Expression *e) {
      return true; //? ???
    }

    void find(std::string callName, Expression *e) {
      _foundCalls.clear();
      _callName = callName;
      TopDownIterator<CallFinder>(*this).run(e);
    }

  };

  class OpReplacer : public EVisitor {
  private:

  public:
    OpReplacer() {}

    void vCall(Call &c) {
      if (c.id().str() == LSConstants::ASSIGN_OP) {
        auto args = c.args();
        assert(args.size() == 2);
        if (args[0]->isa<ArrayAccess>()) {
          auto access = args[0]->dyn_cast<ArrayAccess>();
          auto idxs = access->idx();
          if (idxs.size() == 1) {
            std::vector<Expression *> newArgs;
            newArgs.push_back(access->v());
            newArgs.push_back(idxs[0]);
            newArgs.push_back(args[1]);
            c.id(ASTString(LSConstants::ASSIGN_ARRAY));
            c.args(newArgs);
          } else {
            Expression *newIdx = get1dIndex(c, access, idxs);
            std::vector<Expression *> newArgs;
            std::vector<Expression *> array1dArgs;
            array1dArgs.push_back(access->v());
            newArgs.push_back(new Call(c.loc(), "array1d", array1dArgs));
            newArgs.push_back(newIdx);
            newArgs.push_back(args[1]);
            c.id(ASTString(LSConstants::ASSIGN_ARRAY));
            c.args(newArgs);
          }
        } else if (args[0]->isa<Id>()) {
          c.id(ASTString(LSConstants::ASSIGN));
        } else {
          assert(false);
        }
      } else if (c.id().str() == LSConstants::SWAP_OP) {
        auto args = c.args();
        assert(args.size() == 2);
        if (args[0]->isa<ArrayAccess>() && args[1]->isa<ArrayAccess>()) {
          auto accessLHS = args[0]->dyn_cast<ArrayAccess>();
          auto idxLHS = accessLHS->idx();
          auto accessRHS = args[1]->dyn_cast<ArrayAccess>();
          auto idxRHS = accessRHS->idx();
          if (idxLHS.size() == 1 && idxRHS.size() == 1) {
            std::vector<Expression *> newArgs;
            newArgs.push_back(accessLHS->v());
            newArgs.push_back(idxLHS[0]);
            newArgs.push_back(accessRHS->v());
            newArgs.push_back(idxRHS[0]);
            c.id(ASTString(LSConstants::SWAP_ARRAY));
            c.args(newArgs);
          } else {
            std::vector<Expression *> newArgs;
            std::vector<Expression *> array1dArgsLHS;
            array1dArgsLHS.push_back(accessLHS->v());
            newArgs.push_back(new Call(c.loc(), "array1d", array1dArgsLHS));
            if (idxLHS.size() > 1) {
              newArgs.push_back(get1dIndex(c, accessLHS, idxLHS));
            } else {
              newArgs.push_back(idxLHS[0]);
            }

            std::vector<Expression *> array1dArgsRHS;
            array1dArgsRHS.push_back(accessRHS->v());
            newArgs.push_back(new Call(c.loc(), "array1d", array1dArgsRHS));
            if (idxRHS.size() > 1) {
              newArgs.push_back(get1dIndex(c, accessRHS, idxRHS));
            } else {
              newArgs.push_back(idxRHS[0]);
            }
            c.id(ASTString(LSConstants::SWAP_ARRAY));
            c.args(newArgs);
          }
        } else if (args[0]->isa<Id>() && args[1]->isa<Id>()) {
          c.id(ASTString(LSConstants::SWAP));
        } else {
          assert(false);
        }
      }
    }

    Expression *get1dIndex(const Call &c, const ArrayAccess *access, ASTExprVec <Expression> &idxs) const {
      std::__1::vector<Expression *> idxArgs;
      idxArgs.push_back(access->v());
      Expression *plusExpr = IntLit::a(IntVal(1));
      for (int i = 0; i < idxs.size() - 1; ++i) {

        std::__1::vector<Expression *> minArgs;
        minArgs.push_back(new Call(c.loc(),
                                   "index_set_" + std::__1::to_string(i + 1) + "of" +
                                   std::__1::to_string(idxs.size()), idxArgs));
        BinOp *multExpr = new BinOp(c.loc(), idxs[i], BOT_MINUS,
                                    new Call(c.loc(), "min", minArgs));
        
        for (int j = i+1; j < idxs.size(); ++j) {
          std::__1::vector<Expression *> cardArgs;
          cardArgs.push_back(new Call(c.loc(),
                                      "index_set_" + std::__1::to_string(j + 1) + "of" +
                                      std::__1::to_string(idxs.size()), idxArgs));
          multExpr = new BinOp(c.loc(), multExpr, BOT_MULT,
                               new Call(c.loc(), "card", cardArgs));
        }
        plusExpr = new BinOp(c.loc(), plusExpr, BOT_PLUS, multExpr);
      }
      std::__1::vector<Expression *> minArgs;
      minArgs.push_back(new Call(c.loc(),
                                 "index_set_" + std::__1::to_string(idxs.size()) + "of" +
                                 std::__1::to_string(idxs.size()), idxArgs));
      plusExpr = new BinOp(c.loc(),
                           plusExpr,
                           BOT_PLUS,
                           new BinOp(c.loc(),
                                     idxs[idxs.size() - 1],
                                     BOT_MINUS,
                                     new Call(c.loc(), "min", minArgs)));
      return plusExpr;
    }

  };


  class NeighborhoodAndInitExtracter : public EVisitor {
  private:
    std::vector<Call *> _neighborhoods;
    Call *_init;

  public:
    NeighborhoodAndInitExtracter() : _init(NULL) {}

  public:
    const std::vector<Call *> &get_neighborhoods() const {
      return _neighborhoods;
    }

    Call *get_init() const {
      return _init;
    }

    
    // TODO: change to use union instead of \/
    
    /// Visit binary operator
    void vBinOp(const BinOp &b) {
      if (b.op() != BinOpType::BOT_UNION && b.op() != BinOpType::BOT_AND) {
        throw new SyntaxError(b.loc(), "Other binop than union or AND found.");
      }
      if (b.op() == BinOpType::BOT_UNION) {
        bool lhsCall = b.lhs()->isa<Call>();
        bool rhsCall = b.rhs()->isa<Call>();
        if (lhsCall && b.lhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALLY) {
          throw new SyntaxError(b.loc(), "Found initialization statement in union");
        } else if (rhsCall && b.rhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALLY) {
          throw new SyntaxError(b.loc(), "Found initialization statement in union");
        }
      }
      if (b.op() == BinOpType::BOT_AND) {
        bool lhsCall = b.lhs()->isa<Call>();
        bool rhsCall = b.rhs()->isa<Call>();
        if (lhsCall && b.lhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALLY && rhsCall &&
            b.rhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALLY) {
          throw new SyntaxError(b.loc(), "Too many initially statements in neighborhood declaration.");
        } else if (lhsCall && b.lhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALLY) {
          return;
        } else if (rhsCall && b.rhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALLY) {
          return;
        } else {
          throw new SyntaxError(b.loc(), "AND operator not applied to initially statement.");
        }
      }
    }

    /// Visit call
    void vCall(Call &c) {
      /*if(c.id().str() == LSConstants::MOVES){
        _neighbourhoods.push_back(&c);
      }else if(c.id().str() == LSConstants::INITIALLY){
        if(!_init){
          _init = &c;
        }else{
          throw new SyntaxError(c.loc(),"Too many initially statements in neighbourhood declaration.");
        }
      }else{
        throw new SyntaxError(c.loc(),"Unexpected call to " + (c.id().str()) + "in neighbourhood declaration.");
      }*/
    }

    bool enter(Expression *e) {
      if (e->isa<BinOp>()) {
        auto b = e->dyn_cast<BinOp>();
        if (b->op() != BinOpType::BOT_UNION && b->op() != BinOpType::BOT_AND) {
          return false;
        }
        return true;
      }
      if (e->isa<Call>()) {
        std::string id = e->dyn_cast<Call>()->id().str();
        if (id == LSConstants::MOVES) {
          _neighborhoods.push_back(e->dyn_cast<Call>());
        } else if (id == LSConstants::INITIALLY) {
          if (!_init) {
            _init = (e->dyn_cast<Call>());
          } else {
            throw new SyntaxError(e->loc(), "Too many initially statements in neighborhood declaration.");
          }
        } else {
          throw new SyntaxError(e->loc(), "Unexpected call to " + id + "in neighborhood declaration.");
        }

        /*if((e->dyn_cast<Call>()->id().str() == LSConstants::MOVES) || (e->dyn_cast<Call>()->id().str() == LSConstants::INITIALLY)){
          return true;
        }*/
      }
      return false;
    }

  };

  class NeighborhoodGatherer {
  private:
    Expression *_postcond;
    std::vector<Expression*> _preconds;
    std::vector<VarDecl *> _iteratorVars;
    Expression *_moves;
    Comprehension *_origC;
    EnvI &env;
  protected:

  public:
    NeighborhoodGatherer(Comprehension &c, EnvI &e) : _origC(&c), env(e) {
      for (int i = 0; i < c.n_generators(); ++i) {
        for (int j = 0; j < c.n_decls(i); ++j) {
          const VarDecl *oldVar = c.decl(i, j);
          TypeInst *ti = new TypeInst(c.loc(), Type::varint(), c.in(i));
          VarDecl *newVar = new VarDecl(c.loc(), ti, oldVar->id());
          newVar->introduced(true);
          _iteratorVars.push_back(newVar);
        }
      }
      
      
      for (int i=0; i<c.n_generators(); i++) {
        if(c.where(i)){
          _preconds.push_back(c.where(i));
        }
      }
      
      CallFinder *postcondFinder = new CallFinder();
      postcondFinder->find(LSConstants::POSTCOND, c.e());
      assert((postcondFinder->getFoundCalls().size() <= 1) && "Found multiple ensuring in a neighborhood.");
      if (postcondFinder->getFoundCalls().size() == 1) {
        _postcond = postcondFinder->getFoundCalls()[0]->args()[0];
      } else {
        _postcond = NULL;
      }


      if (c.e()->isa<BinOp>() &&
          (c.e()->dyn_cast<BinOp>())->rhs()->isa<Call>() &&
          (c.e()->dyn_cast<BinOp>())->rhs()->dyn_cast<Call>()->id().str() == LSConstants::POSTCOND) {
        _moves = (c.e()->dyn_cast<BinOp>())->lhs();
      } else {
        _moves = c.e();
      }


      // Replace moves with annotations
      
      OpReplacer m;
      TopDownIterator<OpReplacer>(m).run(_moves);
    }

    Let &getLetExpression(FunctionI *fi, std::string neighborhoodName) {

      Expression *trueLit = constants().lit_true;

      //Construct list of post conditions (it actually has size 1).
      std::vector<Expression *> postcondList;
      if (_postcond) {
        //_postcond->addAnnotation(constants().ann.post_condition);
        postcondList.push_back(_postcond);
      } else {
        postcondList.push_back(trueLit);
      }

      //Construct list of where conditions and iterator variable declarations.
      std::vector<Expression *> precondList;
      if (_iteratorVars.size() > 0) {
        for (auto itr = _iteratorVars.begin(); itr != _iteratorVars.end(); ++itr) {
          (*itr)->addAnnotation(constants().ann.defines_generator);
        }
        precondList.insert(std::end(precondList), std::begin(_iteratorVars), std::end(_iteratorVars));
      }
      
      for (auto itr = _preconds.begin(); itr != _preconds.end(); ++itr) {
        //(*itr)->addAnnotation(constants().ann.pre_condition);
        precondList.push_back((*itr));
      }

      //Construct nested lets


      Let *postcondLet = new Let(_origC->loc(), postcondList, constants().ann.ann_void);
      std::vector<Expression *> callPostcondArgs;
      std::vector<VarDecl *> postcondFuncParam;
      //Add function parameters to function and call
      for (auto itr = fi->params().begin(); itr != fi->params().end(); ++itr) {
        postcondFuncParam.push_back(*itr);
        callPostcondArgs.push_back((*itr)->id());
      }
      //Add declared variables to function and call
      for (auto itvars = _iteratorVars.begin(); itvars != _iteratorVars.end(); ++itvars) {
        VarDecl *origVarDecl = (*itvars);
        TypeInst *origTi = origVarDecl->ti();
        TypeInst *ti = new TypeInst(origTi->loc(), origTi->type());
        VarDecl *d = new VarDecl(origVarDecl->loc(), ti, origVarDecl->id());
        postcondFuncParam.push_back(d);
        callPostcondArgs.push_back((d)->id());
      }

      Type vBool = Type::ann();
      

      Call *postcondCall = LSTransformation::createFlatFunctionAndCall(env,
                                                                     vBool,
                                                                     _origC->loc(),
                                                                     neighborhoodName + "_" + LSConstants::POSTCOND,
                                                                     postcondFuncParam, postcondLet, callPostcondArgs);

      std::vector<Expression *> callReturnAnnArgs;
      callReturnAnnArgs.push_back(postcondCall);

      BinOp *returnAnn = new BinOp(_origC->loc(), _moves, BinOpType::BOT_AND,
                                   new Call(_origC->loc(), LSConstants::POSTCOND, callReturnAnnArgs));
      Let *neighborhoodLet = new Let(_origC->loc(), precondList, returnAnn);

      return *neighborhoodLet;
    }

    void debug() {
      std::cerr << "Debug start:" << std::endl;
      std::cerr << "\tIterators: " << std::endl;
      for (auto itr = _iteratorVars.begin(); itr != _iteratorVars.end(); ++itr) {
        std::cerr << "\t\t" << *(*itr) << std::endl;
      }
      std::cerr << "\tWheres: " << std::endl;
      for (auto itr = _preconds.begin(); itr != _preconds.end(); ++itr) {
        std::cerr << "\t\t" << *(*itr) << std::endl;
      }
      std::cerr << "\tEnsuring: " << *_postcond << std::endl;
      std::cerr << "\tMoves: " << *_moves << std::endl;
      std::cerr << "Debug end:" << std::endl;
    }
  };


  class LSTranslate : public ItemVisitor {
  public:
    EnvI &env;

    LSTranslate(EnvI &env0) : env(env0) {}

    void vFunctionI(FunctionI *fi) {
      bool defines_neighborhood = false;
      for (ExpressionSetIter anns = fi->ann().begin(); anns != fi->ann().end(); ++anns) {
        if ((*anns)->isa<Id>() && (*anns)->cast<Id>()->v().str() == LSConstants::NEIGHBORHOOD_DEFINITION)
          defines_neighborhood = true;
      }
      if (defines_neighborhood) {
        Expression *body = fi->e();

        Call *init = NULL;

        NeighborhoodAndInitExtracter _expr;
        TopDownIterator<NeighborhoodAndInitExtracter>(_expr).run(body);

        init = _expr.get_init();
        int i = 0;
        auto foundCalls = _expr.get_neighborhoods();


        std::vector<Expression *> callNeighborhoodArgs;
        std::vector<VarDecl *> neighborhoodFuncParam;
        //Add function parameters to function and call
        for (auto paramItr = fi->params().begin(); paramItr != fi->params().end(); ++paramItr) {
          neighborhoodFuncParam.push_back(*paramItr);
          callNeighborhoodArgs.push_back((*paramItr)->id());
        }
        Type vAnn = Type::ann();

        std::vector<Expression *> neighborhoods;
        for (auto nItr = foundCalls.begin(); nItr != foundCalls.end(); ++nItr) {
          NeighborhoodGatherer _g(*(((*nItr)->args()[0])->dyn_cast<Comprehension>()),env);
          //_g.debug();

          Expression *neighborhoodBody = &(_g.getLetExpression(fi, fi->id().str() + "_"+LSConstants::MOVES+"_" + std::to_string(i)));

          Call *neighborhoodCall = LSTransformation::createFlatFunctionAndCall(env,
                                                                       vAnn,
                                                                       fi->loc(),
                                                                       fi->id().str() + "_"+LSConstants::MOVES+"_" + std::to_string(i),
                                                                       neighborhoodFuncParam,
                                                                       neighborhoodBody, callNeighborhoodArgs);

          neighborhoods.push_back(neighborhoodCall);
          i++;
        }

        std::vector<Expression *> nDeclArgs;
        nDeclArgs.push_back(new ArrayLit(fi->loc(), neighborhoods));
        
        if (init) {
          Type vAnn = Type::ann();
          std::vector<Expression*> initBody(0);
          initBody.push_back(init->args()[0]);
          
          // Create new init function:
          Call *initCall = LSTransformation::createFlatFunctionAndCall(env,
                                                                       vAnn,
                                                                       fi->loc(),
                                                                       fi->id().str() + "_" + LSConstants::INITIALLY,
                                                                       neighborhoodFuncParam,
                                                                       initBody,
                                                                       constants().ann.ann_void, callNeighborhoodArgs);
          std::vector<Expression*> newInitArgs(1);
          newInitArgs[0] = initCall;
          init->args(newInitArgs);
          nDeclArgs.push_back(init);
        }
        Call *neighborhoodDeclaration = new Call(fi->loc(), LSConstants::NEIGHBORHOOD_DECL, nDeclArgs);
        fi->e(neighborhoodDeclaration);
        fi->ann().add(constants().ann.flat_function);
      }
    }
  };

  static void lstransform(Env &e) {
    GCLock lock;
    LSTranslate _lst(e.envi());
    iterItems<LSTranslate>(_lst, e.model());

    /*
    Printer p(std::cerr, 200);
    std::cerr << "---------------Printing model" << std::endl;
    p.print(e.envi().orig);
    std::cerr << "-------------Printing model done" << std::endl;
     */
  }
};


#endif //LIBMINIZINC_LSTRANSFORMER_H
