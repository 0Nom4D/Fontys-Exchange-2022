import 'package:flutter/material.dart';
import 'package:psv_fan_experience/src/models/competitions.dart';

import 'package:psv_fan_experience/src/widgets/background_container.dart';
import 'package:psv_fan_experience/src/widgets/competition_item.dart';
import 'package:psv_fan_experience/src/widgets/psv_appbar.dart';
import 'package:psv_fan_experience/src/widgets/drawer.dart';

class CompetitionsPage extends StatelessWidget {
  CompetitionsPage({super.key});

  final List<String> currentCompetitions = [
    'assets/images/compselection4.png',
    'assets/images/compselection2.png',
    'assets/images/compselection3.png',
    'assets/images/compselection1.png',
  ];

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: const PSVAppbar(title: 'COMPETITIONS'),
      endDrawer: const PSVDrawer(),
      body: Background(
        child: Center(
          child: SizedBox(
            child: ListView.separated(
              shrinkWrap: true,
              itemBuilder: (context, index) => CompetitionItem(
                imagePath: currentCompetitions[index],
                relatedCompetition: Competition.competitions[index]
              ),
              separatorBuilder: (context, index) => const SizedBox.shrink(),
              itemCount: currentCompetitions.length
            ),
          ),
        ),
      )
    );
  }
}
