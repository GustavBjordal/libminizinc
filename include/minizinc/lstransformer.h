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

  namespace LSConstants{
    static constexpr const char* AND = "neighbourhood_and";
    static constexpr const char* ENSURE = "ensure";
    static constexpr const char* WHERE = "where";
    static constexpr const char* FROM = "from";
    static constexpr const char* INITIALIZE = "initialize";
    static constexpr const char* PRE_COND = "ls_pre_condition";
    static constexpr const char* POST_COND = "ls_post_condition";
    static constexpr const char* DEFINES_GENERATOR = "ls_defines_generator";
    static constexpr const char* MOVE = "ls_move";
    static constexpr const char* NEIGHBOURHOOD_DEFINITION = "neighbourhood_definition";
    static constexpr const char* DUMMY = "dummy";
    static constexpr const char* NEIGHBOURHOOD_DECL = "neighbourhood_declaration";
    static constexpr const char* ASSIGN_OP = "':='";
    static constexpr const char* SWAP_OP = "':=:'";
    static constexpr const char* ASSIGN = "assign";
    static constexpr const char* SWAP = "swap";
    static constexpr const char* ASSIGN_ARRAY = "assign_array";
    static constexpr const char* SWAP_ARRAY = "swap_array";
  };
  
  class CallFinder : public EVisitor {
  private:
    std::string _callName;
    std::vector< Call*> _foundCalls;
  protected:

  public:
    CallFinder():_callName("") {}

    CallFinder(std::string callName):_callName(callName) {    }
    /// Visit call
    void vCall(Call& c) {
      if(c.id().str() == _callName){
        _foundCalls.push_back(&c);
      }
    }

    const std::vector<Call *> &getFoundCalls() const {
      return _foundCalls;
    }

    /// Determine whether to enter node
    bool enter(Expression* e) {
      return true; //? ???
    }

    void find(std::string callName, Expression* e){
      _foundCalls.clear();
      _callName = callName;
      TopDownIterator<CallFinder>(*this).run(e);
    }

  };

  class OpReplacer : public EVisitor {
  private:

  public:
    OpReplacer() {}
    void vCall(Call& c) {
      if(c.id().str() == LSConstants::ASSIGN_OP){
        auto args = c.args();
        assert(args.size() == 2);
        if(args[0]->isa<ArrayAccess>()){
          auto access = args[0]->dyn_cast<ArrayAccess>();
          auto idxs = access->idx();
          if(idxs.size() == 1){
            std::vector<Expression*> newArgs;
            newArgs.push_back(access->v());
            newArgs.push_back(idxs[0]);
            newArgs.push_back(args[1]);
            c.id(ASTString(LSConstants::ASSIGN_ARRAY));
            c.args(newArgs);
          }else{
            Expression *newIdx = get1dIndex(c, access, idxs);
            std::vector<Expression*> newArgs;
            std::vector<Expression*> array1dArgs;
            array1dArgs.push_back(access->v());
            newArgs.push_back(new Call(c.loc(),"array1d",array1dArgs));
            newArgs.push_back(newIdx);
            newArgs.push_back(args[1]);
            c.id(ASTString(LSConstants::ASSIGN_ARRAY));
            c.args(newArgs);
          }
        }else if(args[0]->isa<Id>()){
          c.id(ASTString(LSConstants::ASSIGN));
        }else{
          assert(false);
        }
      }else if(c.id().str() == LSConstants::SWAP_OP){
        auto args = c.args();
        assert(args.size() == 2);
        if(args[0]->isa<ArrayAccess>() && args[1]->isa<ArrayAccess>()){
          auto accessLHS = args[0]->dyn_cast<ArrayAccess>();
          auto idxLHS = accessLHS->idx();
          auto accessRHS = args[1]->dyn_cast<ArrayAccess>();
          auto idxRHS = accessRHS->idx();
          if(idxLHS.size() == 1 && idxRHS.size() == 1){
            std::vector<Expression*> newArgs;
            newArgs.push_back(accessLHS->v());
            newArgs.push_back(idxLHS[0]);
            newArgs.push_back(accessRHS->v());
            newArgs.push_back(idxRHS[0]);
            c.id(ASTString(LSConstants::SWAP_ARRAY));
            c.args(newArgs);
          }else{
            std::vector<Expression*> newArgs;
            std::vector<Expression*> array1dArgsLHS;
            array1dArgsLHS.push_back(accessLHS->v());
            newArgs.push_back(new Call(c.loc(),"array1d",array1dArgsLHS));
            if(idxLHS.size() > 1){
              newArgs.push_back(get1dIndex(c,accessLHS,idxLHS));
            } else {
              newArgs.push_back(idxLHS[0]);
            }

            std::vector<Expression*> array1dArgsRHS;
            array1dArgsRHS.push_back(accessRHS->v());
            newArgs.push_back(new Call(c.loc(),"array1d",array1dArgsRHS));
            if(idxRHS.size() > 1){
              newArgs.push_back(get1dIndex(c,accessRHS,idxRHS));
            } else {
              newArgs.push_back(idxRHS[0]);
            }
            c.id(ASTString(LSConstants::SWAP_ARRAY));
            c.args(newArgs);
          }
        }else if(args[0]->isa<Id>() && args[1]->isa<Id>()){
          c.id(ASTString(LSConstants::SWAP));
        }else{
          assert(false);
        }
      }
    }

    Expression* get1dIndex(const Call &c, const ArrayAccess *access, ASTExprVec <Expression> &idxs) const {
      Expression* plusExpr =  IntLit::a(IntVal(1));
      for (int i = 0; i < idxs.size()-1; ++i) {
              std::__1::vector<Expression*> idxArgs;
              idxArgs.push_back(access->v());
              std::__1::vector<Expression*> minArgs;
              minArgs.push_back(new Call(c.loc(),
                                         "index_set_" + std::__1::to_string(i + 1) + "of" +
                                         std::__1::to_string(idxs.size()), idxArgs));
              BinOp* multExpr = new BinOp(c.loc(), idxs[i], BOT_MINUS,
                                          new Call(c.loc(), "min",minArgs));

              for (int j = i; j < idxs.size()-1; ++j) {
                std::__1::vector<Expression*> cardArgs;
                cardArgs.push_back(new Call(c.loc(),
                                            "index_set_" + std::__1::to_string(j + 1) + "of" +
                                            std::__1::to_string(idxs.size()), idxArgs));
                multExpr = new BinOp(c.loc(), multExpr, BOT_MULT,
                                     new Call(c.loc(),"card", cardArgs));
              }
              plusExpr = new BinOp(c.loc(), plusExpr, BOT_PLUS, multExpr);
            }
      plusExpr = new BinOp(c.loc(), plusExpr, BOT_PLUS, idxs[idxs.size() - 1]);
      return plusExpr;
    }

  };

  
  
  class NeighbourhoodFromAndInitExtracter: public EVisitor{
  private:
    std::vector<Call*> _froms;
    Call* _init;

  public:
    NeighbourhoodFromAndInitExtracter():_init(NULL) {}

  public:
    const std::vector<Call *> &get_froms() const {
      return _froms;
    }

    Call *get_init() const {
      return _init;
    }

    /// Visit binary operator
    void vBinOp(const BinOp& b) {
      if(b.op() != BinOpType::BOT_OR && b.op() != BinOpType::BOT_AND){
        throw new SyntaxError(b.loc(),"Other binop than OR or AND found.");
      }
      if(b.op() == BinOpType::BOT_OR){
        bool lhsCall = b.lhs()->isa<Call>();
        bool rhsCall = b.rhs()->isa<Call>();
        if(lhsCall && b.lhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALIZE){
          throw new SyntaxError(b.loc(),"Found initialization statement in OR");
        }else if(rhsCall && b.rhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALIZE){
          throw new SyntaxError(b.loc(),"Found initialization statement in OR");
        }
      }
      if(b.op() == BinOpType::BOT_AND){
        bool lhsCall = b.lhs()->isa<Call>();
        bool rhsCall = b.rhs()->isa<Call>();
        if(lhsCall && b.lhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALIZE && rhsCall && b.rhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALIZE){
          throw new SyntaxError(b.loc(),"Too many initialize statements in neighbourhood declaration.");
        }else if(lhsCall && b.lhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALIZE){
          return;
        }else if(rhsCall && b.rhs()->dyn_cast<Call>()->id().str() == LSConstants::INITIALIZE){
          return;
        }else{
          throw new SyntaxError(b.loc(),"AND operator not applied to initialize statement.");
        }
      }
    }
    /// Visit call
    void vCall(Call& c) {
      if(c.id().str() == LSConstants::FROM){
        _froms.push_back(&c);
      }else if(c.id().str() == LSConstants::INITIALIZE){
        if(!_init){
          _init = &c;
        }else{
          throw new SyntaxError(c.loc(),"Too many initialize statements in neighbourhood declaration.");
        }
      }else{
        throw new SyntaxError(c.loc(),"Unexpected call to " + (c.id().str()) + "in neighbourhood declaration.");
      }
    }
    
    bool enter(Expression* e) {
      if(e->isa<BinOp>()){
        auto b = e->dyn_cast<BinOp>();
        if(b->op() != BinOpType::BOT_OR && b->op() != BinOpType::BOT_AND){
          return false;
        }
        return true;
      }
      if(e->isa<Call>()){
        if((e->dyn_cast<Call>()->id().str() == LSConstants::FROM) || (e->dyn_cast<Call>()->id().str() == LSConstants::INITIALIZE)){
          return true;
        }
      }
      return false;
    }

  };

  class FromGatherer{
  private:
    Expression* _ensure;
    Expression* _where;
    std::vector<VarDecl*> _iteratorVars;
    Expression* _moves;

    Comprehension* _origC;
  protected:

  public:
    FromGatherer(Comprehension& c) : _origC(&c) {
      for (int i = 0; i < c.n_generators(); ++i) {
        for (int j = 0; j < c.n_decls(i); ++j) {
          const VarDecl* oldVar = c.decl(i,j);
          TypeInst* ti = new TypeInst(c.loc(),Type::varint(),c.in(i));
          VarDecl* newVar = new VarDecl(c.loc(),ti,oldVar->id());
          newVar->introduced(true);
          _iteratorVars.push_back(newVar);
        }
      }
      _where = c.where();
      CallFinder* ensureFinder = new CallFinder();
      ensureFinder->find(LSConstants::ENSURE,c.e());
      assert((ensureFinder->getFoundCalls().size() <= 1) && "Found multiple ensures in a neighbourhood.");
      if(ensureFinder->getFoundCalls().size() == 1){
        _ensure = ensureFinder->getFoundCalls()[0]->args()[0];
      }else{
        _ensure = NULL;
      }

      
      if(c.e()->isa<BinOp>() &&
        (c.e()->dyn_cast<BinOp>())->rhs()->isa<Call>() &&
        (c.e()->dyn_cast<BinOp>())->rhs()->dyn_cast<Call>()->id().str() == LSConstants::ENSURE){
        _moves = (c.e()->dyn_cast<BinOp>())->lhs();
      }else{
        _moves = c.e();
      }

      std::cerr << "   Replacing moves" << std::endl;
      OpReplacer m;
      TopDownIterator<OpReplacer>(m).run(_moves);
      std::cerr << "   Done replacing moves" << std::endl;
    }

    Let& getLetExpression(EnvI& env, FunctionI *fi, std::string neighbourhoodName){

      Expression* trueLit = constants().lit_true;

      //Construct list of ensure conditions (it actually has size 1).
      std::vector<Expression*> ensureList;
      if(_ensure) {
        _ensure->addAnnotation(constants().ann.ls_post_condition);
        ensureList.push_back(_ensure);
      }else{
        ensureList.push_back(trueLit);
      }

      //Construct list of where conditions and iterator variable declarations.
      std::vector<Expression*> whereList;
      if(_iteratorVars.size() > 0) {
        for (auto itr = _iteratorVars.begin(); itr != _iteratorVars.end(); ++itr) {
          (*itr)->addAnnotation(constants().ann.ls_defines_generator);
        }
        whereList.insert(std::end(whereList), std::begin(_iteratorVars), std::end(_iteratorVars));
      }
      if(_where) {
        _where->addAnnotation(constants().ann.ls_pre_condition);
        whereList.push_back(_where);
      }

      //Construct nested lets
      Let* ensureLet = new Let(_origC->loc(), ensureList, constants().ann.ls_dummy);
      //ensureLet->addAnnotation(constants().ann.new_constraint_context);

      std::vector<Expression*> callEnsureArgs;
      std::vector<VarDecl*> ensureFuncParam;
      //Add function parameters to function and call
      for (auto itr = fi->params().begin(); itr != fi->params().end(); ++itr) {
        ensureFuncParam.push_back(*itr);
        callEnsureArgs.push_back((*itr)->id());
      }
      //Add declared variables to function and call
      for(auto itvars = _iteratorVars.begin(); itvars != _iteratorVars.end();++itvars){
        VarDecl* origVarDecl = (*itvars);
        TypeInst* origTi = origVarDecl->ti();
        TypeInst* ti = new TypeInst(origTi->loc(),origTi->type());
        VarDecl *d = new VarDecl(origVarDecl->loc(),ti,origVarDecl->id());
        ensureFuncParam.push_back(d);
        callEnsureArgs.push_back((d)->id());
      }
      
      Type vBool = Type::ann();
      FunctionI* ensureFunction = env.create_function(vBool,neighbourhoodName+"_ENSURE",ensureFuncParam,ensureLet);
      ensureFunction->ann().add(constants().ann.flat_function);
      Call* ensureCall = new Call(_origC->loc(),ensureFunction->id().str(),callEnsureArgs,ensureFunction);
      
      std::vector<Expression*> callEnsureAnnArgs;
      callEnsureAnnArgs.push_back(ensureCall);
      
      BinOp* ensureAnd = new BinOp(_origC->loc(),_moves,BinOpType::BOT_AND,new Call(_origC->loc(),LSConstants::ENSURE,callEnsureAnnArgs));
      Let* whereLet = new Let(_origC->loc(), whereList, ensureAnd);

      return *whereLet;
    }

    void debug(){
      std::cerr << "Debug start:" << std::endl;
      std::cerr << "\tIterators: " << std::endl;
      for (auto itr = _iteratorVars.begin(); itr != _iteratorVars.end(); ++itr) {
        std::cerr << "\t\t" << *(*itr) << std::endl;
      }
      std::cerr << "\tWhere: " << *_where << std::endl;
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
        if((*anns)->isa<Id>() && (*anns)->cast<Id>()->v().str() == LSConstants::NEIGHBOURHOOD_DEFINITION)
          defines_neighbourhood = true;
      }
      if (defines_neighbourhood) {
        Expression *body = fi->e();

        Call* init = NULL;
        
        NeighbourhoodFromAndInitExtracter _expr;
        TopDownIterator<NeighbourhoodFromAndInitExtracter>(_expr).run(body);
        
        init = _expr.get_init();
        int i = 0;
        auto foundCalls = _expr.get_froms();
        
        std::vector<Expression*> froms;
        for(auto itr = foundCalls.begin(); itr != foundCalls.end(); ++itr){
          FromGatherer _g(*(((*itr)->args()[0])->dyn_cast<Comprehension>()));
          _g.debug();
          
          Expression* fromBody = &(_g.getLetExpression(env, fi, fi->id().str()+"_FROM_"+std::to_string(i)));
          
          
          std::vector<Expression*> callFromArgs;
          std::vector<VarDecl*> fromFuncParam;
          //Add function parameters to function and call
          for (auto itr = fi->params().begin(); itr != fi->params().end(); ++itr) {
            fromFuncParam.push_back(*itr);
            callFromArgs.push_back((*itr)->id());
          }
          Type vAnn = Type::ann();
          FunctionI* fromFunction = env.create_function(vAnn,fi->id().str()+"_FROM_"+std::to_string(i),fromFuncParam,fromBody);
          fromFunction->ann().add(constants().ann.flat_function);
          Call* fromCall = new Call(fi->loc(),fromFunction->id().str(),callFromArgs,fromFunction);
          
          froms.push_back(fromCall);
          i++;
        }

        std::vector<Expression*> nDeclArgs;
        nDeclArgs.push_back(new ArrayLit(fi->loc(),froms));
        if(init){
          nDeclArgs.push_back(init);
        }
        Call* neighbourhoodDeclaration = new Call(fi->loc(),LSConstants::NEIGHBOURHOOD_DECL, nDeclArgs);
        fi->e(neighbourhoodDeclaration);
        fi->ann().add(constants().ann.flat_function);
        std::cerr << "Done" <<std::endl;
      }
    }
  };

  static void lstransform(Env& e) {
    GCLock lock;
    LSTranslate _lst(e.envi());
    iterItems<LSTranslate>(_lst,e.model());
    
    Printer p(std::cerr, 200);
    std::cerr << "---------------Printing model"<< std::endl;
    p.print(e.envi().orig);
    std::cerr << "-------------Printing model done"<< std::endl;
  }
};


#endif //LIBMINIZINC_LSTRANSFORMER_H
