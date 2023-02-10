import 'dart:convert';

import 'package:flutter/foundation.dart';

import 'package:flutter_secure_storage/flutter_secure_storage.dart';
import 'package:get_it/get_it.dart';

import 'package:portfolio_capture/models/section_model.dart';
import '../models/portfolio_model.dart';

class PortfolioProvider extends ChangeNotifier {
  List<Portfolio> userPortfolios = [];

  PortfolioProvider() {
    init();
  }

  Future<void> init() async {
    String? storedPortfolios = await GetIt.I<FlutterSecureStorage>().read(
        key: 'portfolios',
    );
    if (storedPortfolios != null) {
      Iterable l = jsonDecode(storedPortfolios);
      userPortfolios = List<Portfolio>.from(l.map((item) => Portfolio.fromJson(item)));
      notifyListeners();
    }
  }

  updateLocalStorage() async {
    try {
      await GetIt.I<FlutterSecureStorage>().write(
          key: 'portfolios',
          value: jsonEncode(
              userPortfolios.map((item) => item.toJson()).toList())
      );
    } catch (err) {
      if (kDebugMode) {
        print(err.toString());
      }
    }
  }

  addPortfolioInList(Portfolio newPortfolio) async {
    userPortfolios.add(newPortfolio);
    await updateLocalStorage();
    notifyListeners();
  }

  addSectionToPortfolioAtIndex(int index, PortfolioSection newSection) async {
    userPortfolios[index].sections.add(newSection);
    await updateLocalStorage();
    notifyListeners();
  }

  setSectionsToPortfolioAtIndex(int index, List<PortfolioSection> newSections) async {
    userPortfolios[index].sections = newSections;
    await updateLocalStorage();
    notifyListeners();
  }

  Portfolio getPortfolioAtIndex(int index) => userPortfolios[index];

  setPortfolioInList(List<Portfolio> newPortfolios) async {
    userPortfolios = newPortfolios;
    await updateLocalStorage();
    notifyListeners();
  }

  modifyPortfolio(int toReplace, Portfolio portfolio) async {
    userPortfolios[toReplace] = portfolio;
    await updateLocalStorage();
    notifyListeners();
  }

  removePortfolioWhere(bool Function(Portfolio) predicate) async {
    List<Portfolio> toRemovePortfolios = userPortfolios.where(predicate).toList();

    for (Portfolio portfolio in toRemovePortfolios) {
      userPortfolios.remove(portfolio);
    }
    await updateLocalStorage();
    notifyListeners();
  }

  removePortfolio(Portfolio portfolio) async {
    userPortfolios.remove(portfolio);
    await updateLocalStorage();
    notifyListeners();
  }

  addSection(int portfolioIndex, PortfolioSection section) async {
    userPortfolios[portfolioIndex].sections.add(section);
    await updateLocalStorage();
    notifyListeners();
  }

  addToPortfolioSection(int portfolioIndex, int sectionIndex, String content) async {
    userPortfolios[portfolioIndex].sections[sectionIndex].content += content;
    await updateLocalStorage();
    notifyListeners();
  }

  updatePortfolioSection(int portfolioIndex, int sectionIndex, String content) async {
    userPortfolios[portfolioIndex].sections[sectionIndex].content = content;
    await updateLocalStorage();
    notifyListeners();
  }

  deleteSection(int portfolioIndex, PortfolioSection section) async {
    userPortfolios[portfolioIndex].sections.remove(section);
    await updateLocalStorage();
    notifyListeners();
  }

  deleteSectionAtIndex(int portfolioIndex, int sectionIndex) async {
    PortfolioSection toRemove = userPortfolios[portfolioIndex].sections[sectionIndex];
    userPortfolios[portfolioIndex].sections.remove(toRemove);
    await updateLocalStorage();
    notifyListeners();
  }

  clearPortfolioList() async {
    userPortfolios.clear();
    await updateLocalStorage();
    notifyListeners();
  }
}