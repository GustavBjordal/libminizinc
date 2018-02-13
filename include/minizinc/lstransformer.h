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
    static constexpr const char *AND = "neighbourhood_and";
    static constexpr const char *ENSURE = "ensure";
    static constexpr const char *WHERE = "where";
    static constexpr const char *FROM = "from";
    static constexpr const char *INITIALIZE = "initialize";
    static constexpr const char *PRE_COND = "ls_pre_condition";
    static constexpr const char *POST_COND = "ls_post_condition";
    static constexpr const char *DEFINES_GENERATOR = "ls_defines_generator";
    static constexpr const char *MOVE = "ls_move";
    static constexpr const char *NEIGHBOURHOOD_DEFINITION = "neighbourhood_definition";
    static constexpr const char *DUMMY = "dummy";
    static constexpr const char *NEIGHBOURHOOD_DECL = "neighbourhood_declaration";
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
      
      std::cerr << "Created new function " << name << " - " << *body << " - " << *function <<std::endl;
      
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
      std::cerr << "Created new function " << name << " - " << *returnE <<std::endl;
      
      for (auto itr = body.begin(); itr != body.end(); ++itr) {
        std::cerr << **itr << std::endl;
      }
      std::cerr << "Function body" <<*functionBody << std::endl;
      
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


  class NeighbourhoodFromAndInitExtracter : public EVisitor {
  private:
    std::vector<Call *> _froms;
    Call *_init;

  public:
    NeighbourhoodFromAndInitExtracter() : _init(NULL) {}

  public:
    const std::vector<Call *> &get_froms() const {
      return _froms;
    }

    Call *get_init() const {
      return _init;
    }

    /// Visit binary operator
    void vBinOp(const BinOp &b) {
      if (b.op() != BinOpType::BOT_OR && b.op() != BinOpType::BOT_AND) {
        throw new SyntaxError(b.loc(), "Other binop than OR or AND found.");
      }
      if (b.op() == BinOpType::BOT_OR) {
        bool lhsCall = b.lhs()->isa<Call>();
        bool rhsCall = b.rhs()->isa<Call>();
        if (lhsCall && b.lhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALIZE) {
          throw new SyntaxError(b.loc(), "Found initialization statement in OR");
        } else if (rhsCall && b.rhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALIZE) {
          throw new SyntaxError(b.loc(), "Found initialization statement in OR");
        }
      }
      if (b.op() == BinOpType::BOT_AND) {
        bool lhsCall = b.lhs()->isa<Call>();
        bool rhsCall = b.rhs()->isa<Call>();
        if (lhsCall && b.lhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALIZE && rhsCall &&
            b.rhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALIZE) {
          throw new SyntaxError(b.loc(), "Too many initialize statements in neighbourhood declaration.");
        } else if (lhsCall && b.lhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALIZE) {
          return;
        } else if (rhsCall && b.rhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALIZE) {
          return;
        } else {
          throw new SyntaxError(b.loc(), "AND operator not applied to initialize statement.");
        }
      }
    }

    /// Visit call
    void vCall(Call &c) {
      /*if(c.id().str() == LSConstants::FROM){
        _froms.push_back(&c);
      }else if(c.id().str() == LSConstants::INITIALIZE){
        if(!_init){
          _init = &c;
        }else{
          throw new SyntaxError(c.loc(),"Too many initialize statements in neighbourhood declaration.");
        }
      }else{
        throw new SyntaxError(c.loc(),"Unexpected call to " + (c.id().str()) + "in neighbourhood declaration.");
      }*/
    }

    bool enter(Expression *e) {
      if (e->isa<BinOp>()) {
        auto b = e->dyn_cast<BinOp>();
        if (b->op() != BinOpType::BOT_OR && b->op() != BinOpType::BOT_AND) {
          return false;
        }
        return true;
      }
      if (e->isa<Call>()) {
        std::string id = e->dyn_cast<Call>()->id().str();
        if (id == LSConstants::FROM) {
          _froms.push_back(e->dyn_cast<Call>());
        } else if (id == LSConstants::INITIALIZE) {
          if (!_init) {
            _init = (e->dyn_cast<Call>());
          } else {
            throw new SyntaxError(e->loc(), "Too many initialize statements in neighbourhood declaration.");
          }
        } else {
          throw new SyntaxError(e->loc(), "Unexpected call to " + id + "in neighbourhood declaration.");
        }

        /*if((e->dyn_cast<Call>()->id().str() == LSConstants::FROM) || (e->dyn_cast<Call>()->id().str() == LSConstants::INITIALIZE)){
          return true;
        }*/
      }
      return false;
    }

  };

  class FromGatherer {
  private:
    Expression *_ensure;
    //Expression *_where;
    std::vector<Expression*> _wheres;
    std::vector<VarDecl *> _iteratorVars;
    Expression *_moves;
    Comprehension *_origC;
    EnvI &env;
  protected:

  public:
    FromGatherer(Comprehension &c, EnvI &e) : _origC(&c), env(e) {
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
          _wheres.push_back(c.where(i));
        }
      }
      
      /*std::vector<Expression*> whereParts;
      
      for (int i=0; i<c.n_generators(); i++) {
        if(c.where(i)){
          whereParts.push_back(c.where(i));
        }
      }
      std::vector<Expression*> forall_args(1);
      forall_args[0] = new ArrayLit(c.loc(),whereParts);
      
      Call* forall_where = new Call(c.loc(), constants().ids.forall, forall_args);
      forall_where->type(Type::varbool());
      forall_where->decl(env.orig->matchFn(env, forall_where, false));
      std::cerr << "does this fix things?" << std::endl;
      std::cerr << *forall_where << std::endl;
       */
      
      // Just keep a list of all where and add them further down.
      // Just remember to add the annotation
      
      
      //_where = forall_where; //c.where(0);
      
      
      CallFinder *ensureFinder = new CallFinder();
      ensureFinder->find(LSConstants::ENSURE, c.e());
      assert((ensureFinder->getFoundCalls().size() <= 1) && "Found multiple ensures in a neighbourhood.");
      if (ensureFinder->getFoundCalls().size() == 1) {
        _ensure = ensureFinder->getFoundCalls()[0]->args()[0];
      } else {
        _ensure = NULL;
      }


      if (c.e()->isa<BinOp>() &&
          (c.e()->dyn_cast<BinOp>())->rhs()->isa<Call>() &&
          (c.e()->dyn_cast<BinOp>())->rhs()->dyn_cast<Call>()->id().str() == LSConstants::ENSURE) {
        _moves = (c.e()->dyn_cast<BinOp>())->lhs();
      } else {
        _moves = c.e();
      }

      std::cerr << "   Replacing moves" << std::endl;
      OpReplacer m;
      TopDownIterator<OpReplacer>(m).run(_moves);
      std::cerr << "   Done replacing moves" << std::endl;
    }

    Let &getLetExpression(FunctionI *fi, std::string neighbourhoodName) {

      Expression *trueLit = constants().lit_true;

      //Construct list of ensure conditions (it actually has size 1).
      std::vector<Expression *> ensureList;
      if (_ensure) {
        _ensure->addAnnotation(constants().ann.ls_post_condition);
        ensureList.push_back(_ensure);
      } else {
        ensureList.push_back(trueLit);
      }

      //Construct list of where conditions and iterator variable declarations.
      std::vector<Expression *> whereList;
      if (_iteratorVars.size() > 0) {
        for (auto itr = _iteratorVars.begin(); itr != _iteratorVars.end(); ++itr) {
          (*itr)->addAnnotation(constants().ann.ls_defines_generator);
        }
        whereList.insert(std::end(whereList), std::begin(_iteratorVars), std::end(_iteratorVars));
      }
      
      for (auto itr = _wheres.begin(); itr != _wheres.end(); ++itr) {
        (*itr)->addAnnotation(constants().ann.ls_pre_condition);
        whereList.push_back((*itr));
      }
      /*
      if (_where) {
        _where->addAnnotation(constants().ann.ls_pre_condition);
        whereList.push_back(_where);
      }
       */

      //Construct nested lets


      Let *ensureLet = new Let(_origC->loc(), ensureList, constants().ann.ls_dummy);
      std::vector<Expression *> callEnsureArgs;
      std::vector<VarDecl *> ensureFuncParam;
      //Add function parameters to function and call
      for (auto itr = fi->params().begin(); itr != fi->params().end(); ++itr) {
        ensureFuncParam.push_back(*itr);
        callEnsureArgs.push_back((*itr)->id());
      }
      //Add declared variables to function and call
      for (auto itvars = _iteratorVars.begin(); itvars != _iteratorVars.end(); ++itvars) {
        VarDecl *origVarDecl = (*itvars);
        TypeInst *origTi = origVarDecl->ti();
        TypeInst *ti = new TypeInst(origTi->loc(), origTi->type());
        VarDecl *d = new VarDecl(origVarDecl->loc(), ti, origVarDecl->id());
        ensureFuncParam.push_back(d);
        callEnsureArgs.push_back((d)->id());
      }

      Type vBool = Type::ann();
      
      /*FunctionI *ensureFunction = env.create_function(vBool, neighbourhoodName + "_ENSURE", ensureFuncParam, ensureLet);
      ensureFunction->ann().add(constants().ann.flat_function);
      Call *ensureCall = new Call(_origC->loc(), ensureFunction->id().str(), callEnsureArgs, ensureFunction);
      */

      Call *ensureCall = LSTransformation::createFlatFunctionAndCall(env,
                                                                     vBool,
                                                                     _origC->loc(),
                                                                     neighbourhoodName + "_ENSURE",
                                                                     ensureFuncParam, ensureLet, callEnsureArgs);

      std::vector<Expression *> callEnsureAnnArgs;
      callEnsureAnnArgs.push_back(ensureCall);

      BinOp *ensureAnd = new BinOp(_origC->loc(), _moves, BinOpType::BOT_AND,
                                   new Call(_origC->loc(), LSConstants::ENSURE, callEnsureAnnArgs));
      Let *whereLet = new Let(_origC->loc(), whereList, ensureAnd);

      return *whereLet;
    }

    void debug() {
      std::cerr << "Debug start:" << std::endl;
      std::cerr << "\tIterators: " << std::endl;
      for (auto itr = _iteratorVars.begin(); itr != _iteratorVars.end(); ++itr) {
        std::cerr << "\t\t" << *(*itr) << std::endl;
      }
      std::cerr << "\tWheres: " << std::endl;
      for (auto itr = _wheres.begin(); itr != _wheres.end(); ++itr) {
        std::cerr << "\t\t" << *(*itr) << std::endl;
      }
      std::cerr << "\tEnsure: " << *_ensure << std::endl;
      std::cerr << "\tMoves: " << *_moves << std::endl;
      std::cerr << "Debug end:" << std::endl;
    }
  };


  class LSTranslate : public ItemVisitor {
  public:
    EnvI &env;

    LSTranslate(EnvI &env0) : env(env0) {}

    void vFunctionI(FunctionI *fi) {
      bool defines_neighbourhood = false;
      for (ExpressionSetIter anns = fi->ann().begin(); anns != fi->ann().end(); ++anns) {
        if ((*anns)->isa<Id>() && (*anns)->cast<Id>()->v().str() == LSConstants::NEIGHBOURHOOD_DEFINITION)
          defines_neighbourhood = true;
      }
      if (defines_neighbourhood) {
        Expression *body = fi->e();

        Call *init = NULL;

        NeighbourhoodFromAndInitExtracter _expr;
        TopDownIterator<NeighbourhoodFromAndInitExtracter>(_expr).run(body);

        init = _expr.get_init();
        int i = 0;
        auto foundCalls = _expr.get_froms();


        std::vector<Expression *> callFromArgs;
        std::vector<VarDecl *> fromFuncParam;
        //Add function parameters to function and call
        for (auto paramItr = fi->params().begin(); paramItr != fi->params().end(); ++paramItr) {
          fromFuncParam.push_back(*paramItr);
          callFromArgs.push_back((*paramItr)->id());
        }
        Type vAnn = Type::ann();

        std::vector<Expression *> froms;
        for (auto fromItr = foundCalls.begin(); fromItr != foundCalls.end(); ++fromItr) {
          FromGatherer _g(*(((*fromItr)->args()[0])->dyn_cast<Comprehension>()),env);
          _g.debug();

          Expression *fromBody = &(_g.getLetExpression(fi, fi->id().str() + "_FROM_" + std::to_string(i)));


          /*FunctionI *fromFunction = env.create_function(vAnn, fi->id().str() + "_FROM_" + std::to_string(i),
                                                        fromFuncParam, fromBody);
          fromFunction->ann().add(constants().ann.flat_function);
          Call *fromCall = new Call(fi->loc(), fromFunction->id().str(), callFromArgs, fromFunction);
          */
          Call *fromCall = LSTransformation::createFlatFunctionAndCall(env,
                                                                       vAnn,
                                                                       fi->loc(),
                                                                       fi->id().str() + "_FROM_" + std::to_string(i),
                                                                       fromFuncParam,
                                                                       fromBody, callFromArgs);

          froms.push_back(fromCall);
          i++;
        }

        std::vector<Expression *> nDeclArgs;
        nDeclArgs.push_back(new ArrayLit(fi->loc(), froms));
        if (init) {
          std::cerr << "Has init" << *init << std::endl;
          
          Type vAnn = Type::ann();
          std::vector<Expression*> initBody(0);
          std::cerr << "Arg is" << *init->args()[0] << std::endl;
          initBody.push_back(init->args()[0]);
          Call *initCall = LSTransformation::createFlatFunctionAndCall(env,
                                                                       vAnn,
                                                                       fi->loc(),
                                                                       fi->id().str() + "_INITALIZE",
                                                                       fromFuncParam,
                                                                       initBody,
                                                                       constants().ann.ls_dummy, callFromArgs);
          std::cerr << "Created new call" << *initCall << std::endl;
          std::cerr << "Created new Function" << *initCall->decl() << std::endl;
          std::vector<Expression*> newInitArgs(1);
          newInitArgs[0] = initCall;
          init->args(newInitArgs);
          nDeclArgs.push_back(init);
        }
        Call *neighbourhoodDeclaration = new Call(fi->loc(), LSConstants::NEIGHBOURHOOD_DECL, nDeclArgs);
        fi->e(neighbourhoodDeclaration);
        fi->ann().add(constants().ann.flat_function);
        std::cerr << "Done" << std::endl;
      }
    }
  };

  static void lstransform(Env &e) {
    GCLock lock;
    LSTranslate _lst(e.envi());
    iterItems<LSTranslate>(_lst, e.model());

    Printer p(std::cerr, 200);
    std::cerr << "---------------Printing model" << std::endl;
    p.print(e.envi().orig);
    std::cerr << "-------------Printing model done" << std::endl;
  }
};


#endif //LIBMINIZINC_LSTRANSFORMER_H
