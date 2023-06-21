import 'package:flutter/material.dart';

import 'package:go_router/go_router.dart';

import 'package:psv_fan_experience/src/models/competitions.dart';

class CompetitionItem extends StatelessWidget {
  final String imagePath;
  final Competition relatedCompetition;

  const CompetitionItem({
    super.key,
    required this.imagePath,
    required this.relatedCompetition
  });

  @override
  Widget build(BuildContext context) {
    const double baseWidth = 390;
    final double fem = MediaQuery.of(context).size.width / baseWidth;

    return Padding(
      padding: const EdgeInsets.only(top: 10, bottom: 5),
      child: Container(
        margin: EdgeInsets.fromLTRB(0 * fem, 0 * fem, 2 * fem, 23 * fem),
        child: TextButton(
          onPressed: () => GoRouter.of(context).go('/competitions/${relatedCompetition.name}'),
          style: TextButton.styleFrom(padding: EdgeInsets.zero),
          child: SizedBox(
            width: 327 * fem,
            height: 149 * fem,
            child: Image.asset(
              imagePath,
              fit: BoxFit.cover,
            ),
          ),
        ),
      ),
    );
  }
}
