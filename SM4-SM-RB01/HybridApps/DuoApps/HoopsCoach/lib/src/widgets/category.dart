import 'package:flutter/material.dart';

class AnalysisCategory extends StatelessWidget {
  const AnalysisCategory({required this.categoryTitle, required this.description, Key? key}) : super(key: key);

  final String categoryTitle;
  final String description;

  @override
  Widget build(BuildContext context) {
    return Column(
      mainAxisAlignment: MainAxisAlignment.center,
      children: [
        Text(
          categoryTitle,
          textAlign: TextAlign.start,
          style: const TextStyle(
            color: Colors.white,
            fontSize: 25,
            fontWeight: FontWeight.bold
          ),
        ),
        Text(
          description,
          textAlign: TextAlign.start,
          style: const TextStyle(
            color: Colors.red,
            fontSize: 40,
            fontWeight: FontWeight.bold
          ),
        ),
      ],
    );
  }
}