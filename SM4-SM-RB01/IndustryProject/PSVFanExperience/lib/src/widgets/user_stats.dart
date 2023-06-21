import 'package:flutter/material.dart';
import 'package:psv_fan_experience/src/widgets/profile_statistic_widget.dart';

import 'package:psv_fan_experience/src/models/profile_statistic.dart';
import 'package:psv_fan_experience/src/models/statistic.dart';

class UserStats extends StatelessWidget {
  final int points;
  final int awards;
  final int submissions;

  const UserStats({
    Key? key,
    required this.points,
    required this.awards,
    required this.submissions,
  }) : super(key: key);

  UserStats.from(Statistics model, {super.key})
    : points = model.points,
      awards = model.awards,
      submissions = model.submissions;

  @override
  Widget build(BuildContext context) {
    return Row(
      mainAxisAlignment: MainAxisAlignment.spaceBetween,
      children: [
        ProfileStatisticWidget(
          profileStatistic: ProfileStatistic('Points', points),
        ),
        ProfileStatisticWidget(
          profileStatistic: ProfileStatistic('Awards', awards),
        ),
        ProfileStatisticWidget(
          profileStatistic: ProfileStatistic('Submissions', submissions),
        )
      ],
    );
  }

}
