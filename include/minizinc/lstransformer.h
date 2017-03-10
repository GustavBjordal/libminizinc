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
#include <minizinc/model.hh>
#include <minizinc/astiterator.hh>
#include <minizinc/model.hh>
#include <minizinc/astexception.hh>
#include <minizinc/copy.hh>
#include "ast.hh"

namespace MiniZinc {

  class LSConstants{
  public:
    static constexpr const char* AND = "neighbourhood_and";
    static constexpr const char* ENSURE = "ensure";
    static constexpr const char* WHERE = "where";
    static constexpr const char* FROM = "from";
    static constexpr const char* INITIALIZE = "initialize";
    static constexpr const char* PRE_COND = "ls_pre_condition";
    static constexpr const char* POST_COND = "ls_post_condition";
    static constexpr const char* DEFINES_GENERATOR = "ls_defines_generator";
    static constexpr const char* NEIGHBOURHOOD_DEFINITION = "neighbourhood_definition";
    static constexpr const char* DUMMY = "dummy";
    static constexpr const char* NEIGHBOURHOOD_DECL = "neighbourhood_declaration";
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

  /*class IdReplacer : public EVisitor {
  private:
    Id* _target;
    VarDecl* _newDecl;
  public:
    IdReplacer(Id& oldId, VarDecl& newDecl):_target(&oldId), _newDecl(&newDecl) {    }
    /// Visit call
    void vId(Id& i) {
      if(i.str() == _target->str()) {
        i.decl(_newDecl);
      }
    }
  };*/

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

      if(c.e()->isa<Call>() && (c.e()->dyn_cast<Call>())->id().str() == LSConstants::AND){
        auto callArgs = (c.e()->dyn_cast<Call>())->args();
        assert(callArgs.size() == 2 && "Wrong number of arguments to cbls and");
        //If we have an ensure
        if(callArgs[1]->isa<Call>() && (callArgs[1]->dyn_cast<Call>())->id().str() == LSConstants::ENSURE){
          _moves = callArgs[0];
        }else{
          _moves = c.e();
        }
        /*for(auto itr = callArgs.begin(); itr != callArgs.end(); ++itr){
          if((*itr)->isa<Call>() && ((*itr)->dyn_cast<Call>())->id().str() == "ensure")
            continue;
          _moves.push_back(*itr);
        }*/
      }else{
        _moves = c.e();
      }
      std::cerr << *(c.e()) << std::endl;
    }

    Let& getLetExpression(VarDecl& dummy){

      std::vector<Expression*>* dummyArg = new std::vector<Expression*>();
      dummyArg->push_back(dummy.id());
      Expression* trueLit = constants().lit_true;

      //Construct list of ensure conditions (it actually has size 1).
      std::vector<Expression*>* ensureList = new std::vector<Expression*>();
      if(_ensure) {
        _ensure->addAnnotation(new Call(_ensure->loc(),LSConstants::POST_COND,*dummyArg));
        ensureList->push_back(_ensure);
      }else{
        ensureList->push_back(trueLit);
      }

      //Construct list of where conditions and iterator variable declarations.
      std::vector<Expression*>* whereList = new std::vector<Expression*>();
      whereList->push_back(&dummy);
      if(_iteratorVars.size() > 0) {
        for (auto itr = _iteratorVars.begin(); itr != _iteratorVars.end(); ++itr) {
          (*itr)->addAnnotation(new Call((*itr)->loc(), LSConstants::DEFINES_GENERATOR, *dummyArg));
        }
        whereList->insert(std::end(*whereList), std::begin(_iteratorVars), std::end(_iteratorVars));
      }
      if(_where) {
        _where->addAnnotation(new Call(_where->loc(),LSConstants::PRE_COND,*dummyArg));
        whereList->push_back(_where);
      }

      //Construct nested lets let s
      Let* ensureLet = new Let(_origC->loc(), *ensureList, _moves);
      ensureLet->addAnnotation(constants().ann.new_constraint_context);
      Let* whereLet = new Let(_origC->loc(), *whereList, ensureLet);
      whereLet->addAnnotation(constants().ann.new_constraint_context);

      std::cerr << *whereLet << std::endl;
      return *whereLet;
    }

    void debug(){
      std::cerr << "Debug start:" << std::endl;
      std::cerr << "Iterators: " << std::endl;
      for (auto itr = _iteratorVars.begin(); itr != _iteratorVars.end(); ++itr) {
        std::cerr << "  " << *(*itr) << std::endl;
      }
      std::cerr << "Where: " << *_where << std::endl;
      std::cerr << "Ensure: " << *_ensure << std::endl;
      std::cerr << "Moves: " << *_moves << std::endl;
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
        std::cerr << *body << std::endl;

        Call* init = NULL;
        if(body->isa<Call>() && body->dyn_cast<Call>()->id().str() == LSConstants::AND){
          Call* andBody = body->dyn_cast<Call>();
          //Second argument of an and at the "root" level of a neighbourhood must be the initialize
          assert(andBody->args()[1]->isa<Call>() && andBody->args()[1]->dyn_cast<Call>()->id().str() == LSConstants::INITIALIZE);
          init = andBody->args()[1]->dyn_cast<Call>();
          body = andBody->args()[0];
        }

        std::vector<Expression*>* froms = new std::vector<Expression*>();

        CallFinder _from(LSConstants::FROM);
        TopDownIterator<CallFinder>(_from).run(body);
        auto foundCalls = _from.getFoundCalls();
        for(auto itr = foundCalls.begin(); itr != foundCalls.end(); ++itr){
          std::cerr << " A generator" << std::endl;
          FromGatherer _g(*(((*itr)->args()[0])->dyn_cast<Comprehension>()));
          _g.debug();
          TypeInst* ti = new TypeInst((*itr)->loc(),Type::varbool());
          VarDecl* dummy = new VarDecl((*itr)->loc(),ti,LSConstants::DUMMY);
          dummy->introduced(true);
          dummy->addAnnotation(constants().ann.ls_dummy);
          froms->push_back(&(_g.getLetExpression(*dummy)));
          std::cerr << "Warning: The current implementation does not check that each from is separated by an \\/ operator." << std::endl;
        }

        std::vector<Expression*>* nDeclArgs = new std::vector<Expression*>();
        nDeclArgs->push_back(new ArrayLit(fi->loc(),*froms));
        if(init)
          nDeclArgs->push_back(init);
        Call* neighbourhoodDeclaration = new Call(fi->loc(),LSConstants::NEIGHBOURHOOD_DECL, *nDeclArgs);
        fi->e(neighbourhoodDeclaration);
        std::cerr << "Done" <<std::endl;
      }
    }
  };



  void lstransform(Env& e) {
    GCLock lock;
    LSTranslate _lst(e.envi());
    iterItems<LSTranslate>(_lst,e.model());;

  }
};

/*
 class NeighbourhoodDefinitionVisitor : public EVisitor {
  protected:

  public:
    /// Visit call
    void vCall(const Call& c) {
      std::cerr << "Call: " << c << std::endl;
    }
    /// Visit array comprehension
    void vComprehension(Comprehension& c) {

      std::cerr << "Comp: " << *c.e() << " | ";
      for (int i = 0; i < c.n_generators(); ++i) {
        for (int j = 0; j < c.n_decls(i); ++j) {
          const VarDecl* oldVar = c.decl(i,j);
          TypeInst* ti = new TypeInst(c.loc(),Type::varint(),c.in(i));
          VarDecl* newVar = new VarDecl(c.loc(),ti,oldVar->id());
          std::cerr << newVar << ",";
        }
      }

      std::cerr << " where  " << *c.where() << std::endl;
    }
    /// Determine whether to enter node
    bool enter(Expression* e) {
      return true; //? ???
    }
  };
 */

#endif //LIBMINIZINC_LSTRANSFORMER_H
