/**
 * This file is part of sally.
 * Copyright (C) 2015 SRI International.
 *
 * Sally is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Sally is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sally.  If not, see <http://www.gnu.org/licenses/>.
 */

#pragma once

#include <cassert>
#include <iosfwd>

namespace sally {
namespace utils {

template <typename T>
class smart_ptr {

  /** Object to capture T and a smart_ptr count */
  class T_counted {
    T* d_obj;
    size_t d_smart_ptrcount;
  public:
    T_counted(T* obj);
    ~T_counted();
    void attach();
    void detach();
    T* get();
    const T* get() const;
  };

  T_counted* d_obj;

public:

  smart_ptr();
  smart_ptr(T* obj);
  smart_ptr(const smart_ptr& r);
  ~smart_ptr();
  smart_ptr& operator = (const smart_ptr& other);
  smart_ptr& operator = (T* obj);
  T& operator * ();
  const T& operator * () const;
  T* operator -> ();
  const T* operator -> () const;
  bool operator < (const smart_ptr& other) const;
  operator bool () const { return d_obj; }
};

template <typename T>
smart_ptr<T>::T_counted::T_counted(T* obj)
: d_obj(obj)
, d_smart_ptrcount(0)
{
  attach();
}

template <typename T>
smart_ptr<T>::T_counted::~T_counted() {
  assert(d_smart_ptrcount == 0);
}

template <typename T>
T* smart_ptr<T>::T_counted::get() {
  return d_obj;
}

template <typename T>
const T* smart_ptr<T>::T_counted::get() const {
  return d_obj;
}

template <typename T>
void smart_ptr<T>::T_counted::attach() {
  d_smart_ptrcount ++;
}

template <typename T>
void smart_ptr<T>::T_counted::detach() {
  assert(d_smart_ptrcount > 0);
  d_smart_ptrcount --;
  if (d_smart_ptrcount == 0) {
    delete d_obj;
    delete this;
  }
}

template <typename T>
smart_ptr<T>::smart_ptr::smart_ptr()
: d_obj(0)
{}

template <typename T>
smart_ptr<T>::smart_ptr(T* obj)
: d_obj(0)
{
  if (obj) {
    d_obj = new T_counted(obj);
  }
}

template <typename T>
smart_ptr<T>::smart_ptr(const smart_ptr& r)
: d_obj(r.d_obj)
{
  if (d_obj) {
    d_obj->attach();
  }
}

template <typename T>
smart_ptr<T>::~smart_ptr() {
  if (d_obj) {
    d_obj->detach();
  }
}

template <typename T>
smart_ptr<T>& smart_ptr<T>::operator = (const smart_ptr<T>& other)
{
  if (this != &other) {
    if (d_obj) {
      d_obj->detach();
    }
    d_obj = other.d_obj;
    if (d_obj) {
      d_obj->attach();
    }
  }
  return *this;
}

template <typename T>
smart_ptr<T>& smart_ptr<T>::operator = (T* m)
{
  if (d_obj) {
    d_obj->detach();
    d_obj = 0;
  }
  if (m) {
    d_obj = new T_counted(m);
  }
  return *this;
}

template <typename T>
T& smart_ptr<T>::operator * () {
  assert(d_obj);
  return *d_obj->get();
}

template <typename T>
const T& smart_ptr<T>::operator * () const {
  assert(d_obj);
  return *d_obj->get();
}

template <typename T>
T* smart_ptr<T>::operator -> () {
  assert(d_obj);
  return d_obj->get();
}

template <typename T>
const T* smart_ptr<T>::operator -> () const {
  return d_obj->get();
}

template <typename T>
bool smart_ptr<T>::operator < (const smart_ptr& other) const {
  return d_obj->get() < other.d_obj->get();
}

}
}
