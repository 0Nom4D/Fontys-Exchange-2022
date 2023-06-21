import 'package:flutter/material.dart';

import 'package:fl_chart/fl_chart.dart';

import 'package:app/src/widgets/video_section.dart';
import 'package:app/src/widgets/info_box.dart';

class ProgressView extends StatefulWidget {
  const ProgressView({super.key});

  @override
  ProgressViewState createState() => ProgressViewState();
}

class ProgressViewState extends State<ProgressView> {
  Widget bottomTitleWidgets(double value, TitleMeta meta) {
    const style = TextStyle(
      fontWeight: FontWeight.bold,
      color: Colors.white,
      fontSize: 16,
    );

    Widget text;
    switch (value.toInt()) {
      case 2:
        text = const Text('2nd', style: style);
        break;
      case 7:
        text = const Text('7th', style: style);
        break;
      case 12:
        text = const Text('12th', style: style);
        break;
      default:
        text = const Text('');
        break;
    }

    return SideTitleWidget(
      axisSide: meta.axisSide,
      space: 10,
      child: text,
    );
  }

  Widget leftTitleWidgets(double value, TitleMeta meta) {
    const style = TextStyle(
      fontWeight: FontWeight.bold,
      color: Colors.white,
      fontSize: 14,
    );

    String text;
    switch (value.toInt()) {
      case 20:
        text = '20';
        break;
      case 40:
        text = '40';
        break;
      case 60:
        text = '60';
        break;
      case 80:
        text = '80';
        break;
      case 100:
        text = '100';
        break;
      default:
        return Container();
    }

    return Text(text, style: style, textAlign: TextAlign.center);
  }

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        automaticallyImplyLeading: false,
        title: const Text(
          "",
          style: TextStyle(
            color: Colors.black,
            fontWeight: FontWeight.bold,
            fontSize: 40,
          )
        ),
        backgroundColor: Colors.transparent,
      ),
      body: SingleChildScrollView(
        child: Padding(
          padding: const EdgeInsets.symmetric(vertical: 10, horizontal: 15),
          child: Column(
            crossAxisAlignment: CrossAxisAlignment.start,
            children: [
              const Text(
                "Progress",
                textAlign: TextAlign.start,
                style: TextStyle(
                  color: Colors.white,
                  fontSize: 40,
                  fontWeight: FontWeight.bold
                ),
              ),
              const VideoSection(title: "Three Pointer Accuracy", asset: "accuracy_practice"),
              Card(
                shape: RoundedRectangleBorder(
                    borderRadius: BorderRadius.circular(15)
                ),
                color: Colors.white.withOpacity(.24),
                child: Padding(
                  padding: const EdgeInsets.symmetric(vertical: 16.0, horizontal: 8.0),
                  child: SizedBox(
                    height: MediaQuery.of(context).size.height * 0.25,
                    width: MediaQuery.of(context).size.width,
                    child: LineChart(
                      LineChartData(
                        minX: 0,
                        minY: 0,
                        maxX: 16,
                        maxY: 100,
                        gridData: FlGridData(show: true),
                        borderData: FlBorderData(
                          show: true,
                          border: Border(
                            bottom: BorderSide(color: Colors.grey.withOpacity(0.6), width: 4),
                            left: const BorderSide(color: Colors.transparent),
                            right: const BorderSide(color: Colors.transparent),
                            top: const BorderSide(color: Colors.transparent),
                          ),
                        ),
                        titlesData: FlTitlesData(
                          bottomTitles: AxisTitles(
                            sideTitles: SideTitles(
                              showTitles: true,
                              reservedSize: 32,
                              interval: 1,
                              getTitlesWidget: bottomTitleWidgets,
                            ),
                          ),
                          rightTitles: AxisTitles(
                            sideTitles: SideTitles(showTitles: false),
                          ),
                          topTitles: AxisTitles(
                            sideTitles: SideTitles(showTitles: false),
                          ),
                          leftTitles: AxisTitles(
                            sideTitles: SideTitles(
                              getTitlesWidget: leftTitleWidgets,
                              showTitles: true,
                              interval: 1,
                              reservedSize: 40,
                            ),
                          ),
                        ),
                        lineTouchData: LineTouchData(
                          handleBuiltInTouches: true,
                          touchTooltipData: LineTouchTooltipData(
                            tooltipBgColor: Colors.blueGrey.withOpacity(0.8),
                          ),
                        ),
                        lineBarsData: [
                          LineChartBarData(
                            isCurved: true,
                            color: Colors.white,
                            barWidth: 4,
                            isStrokeCapRound: true,
                            dotData: FlDotData(show: false),
                            belowBarData: BarAreaData(show: false),
                            spots: const [
                              FlSpot(1, 20),
                              FlSpot(3, 35),
                              FlSpot(5, 45),
                              FlSpot(7, 30),
                              FlSpot(9, 55),
                              FlSpot(10, 80),
                              FlSpot(11, 100),
                              FlSpot(13, 70),
                              FlSpot(14, 85),
                              FlSpot(15, 65),
                              FlSpot(16, 40),
                            ],
                          ),
                          LineChartBarData(
                            isCurved: true,
                            color: Colors.red,
                            barWidth: 4,
                            isStrokeCapRound: true,
                            dotData: FlDotData(show: false),
                            belowBarData: BarAreaData(show: false),
                            spots: const [
                              FlSpot(1, 60),
                              FlSpot(3, 35),
                              FlSpot(5, 50),
                              FlSpot(7, 80),
                              FlSpot(10, 50),
                              FlSpot(12, 35),
                              FlSpot(14, 65),
                              FlSpot(15, 100),
                              FlSpot(16, 75),
                            ],
                          )
                        ]
                      ),
                      swapAnimationDuration: const Duration(milliseconds: 250)
                    ),
                  ),
                ),
              ),
              const SizedBox(height: 10),
              Row(
                mainAxisAlignment: MainAxisAlignment.spaceAround,
                children: const [
                  InfoBox(title: 'Elbow Release', description: '20°', icon: Icons.square_foot),
                  InfoBox(title: 'Hoops Made', description: '8/12', icon: Icons.score)
                ],
              )
            ],
          )
        ),
      )
    );
  }
}
