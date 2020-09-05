use std::cell::RefCell;
use std::collections::{ HashMap, BTreeSet };

use crate::data::subst;


pub type Type = Vec<String>;
pub type Expr = Vec<String>;

pub type Signature = (Type, Option<Expr>);


#[derive(Clone, Debug)]
pub struct Scope {
    items: HashMap<String, Signature>,

    equalities: RefCell<BTreeSet<BTreeSet<Expr>>>,
}

impl Scope {
    pub fn new() -> Scope {
        Scope {
            items: HashMap::new(),
            equalities: RefCell::new(BTreeSet::new()),
        }
    }

    pub fn get_items(&self) -> &HashMap<String, Signature> {
        &self.items
    }

    pub fn contains_item(&self, name: &str) -> bool {
        self.items.contains_key(name)
    }

    pub fn gen_fresh(&self, mut name: String) -> String {
        while self.items.contains_key(&name) {
            name += "`";
        }

        name
    }

    fn rename_fresh(&mut self, name: &str) {
        let val = self.items.remove(name).unwrap();

        let new_name = self.gen_fresh(name.to_string());

        for (ref mut ty, ref mut val) in self.items.values_mut() {
            subst(ty, name, new_name.clone());

            val
                .as_mut()
                .map(
                    |v|
                        subst(v, name, new_name.clone())
                );
        }

        self.items.insert(new_name, val);
    }

    pub fn insert(&mut self, name: String, val: Signature) -> Option<Signature> {
        if self.items.contains_key(&name) {
            self.rename_fresh(&name);
        }

        self.items.insert(name, val)
    }

    pub fn remove(&mut self, name: &str) -> Option<Signature> {
        self.items.remove(name)
    }

    pub fn get(&self, name: &str) -> Option<&Signature> {
        self.items.get(name)
    }

    pub fn get_mut(&mut self, name: &str) -> Option<&mut Signature> {
        self.items.get_mut(name)
    }

    pub fn new_eq_class(&self, val: Expr) {
        self.equalities.borrow_mut().insert({
            let mut tmp = BTreeSet::new();

            tmp.insert(val);

            tmp
        });
    }

    pub fn add_eq(&self, representant: &Expr, new_member: Expr) {
        let mut family = None;

        {
            let eq_bor = self.equalities.borrow_mut();

            for eqs in eq_bor.iter() {
                if eqs.contains(representant) {
                    family = Some(eqs.clone());

                    break;
                }
            }
        }

        if let Some(mut family) = family {
            self.equalities.borrow_mut().remove(&family);

            family.insert(new_member);

            self.equalities.borrow_mut().insert(family);
        }
    }

    pub fn reduce(&self, expr: &Expr) -> Option<Expr> {
        for eqs in self.equalities.borrow().iter() {
            if eqs.contains(expr) {
                return eqs.first().cloned();
            }
        }

        None
    }
}